{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wno-unused-matches -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Test.QuickCheck.ContractModel.ThreatModel where

import Cardano.Api
import Cardano.Api.Byron
import Cardano.Api.Shelley
import Cardano.Ledger.Alonzo.Tx qualified as Ledger (Data, hashData, indexOf)
import Cardano.Ledger.Alonzo.TxWitness qualified as Ledger
import Cardano.Ledger.Babbage.TxBody qualified as Ledger
import Cardano.Ledger.Crypto (StandardCrypto)
import Cardano.Ledger.Keys (coerceKeyRole, hashKey)
import Cardano.Ledger.Serialization qualified as CBOR
import Cardano.Ledger.Shelley.TxBody (Wdrl (..), WitVKey (..))
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import Cardano.Ledger.TxIn (txid)
import Cardano.Slotting.Slot (EpochSize (EpochSize))
import Cardano.Slotting.Time (SlotLength, SystemStart (SystemStart), mkSlotLength)
import Data.Coerce
import Ouroboros.Consensus.Cardano.Block (CardanoEras)
import Ouroboros.Consensus.HardFork.History
import Ouroboros.Consensus.Util.Counting (NonEmpty (NonEmptyOne))

import PlutusTx (ToData, toData)
import PlutusTx.Prelude (BuiltinByteString)

import Control.Monad

import Cardano.Ledger.Alonzo.Scripts qualified as Ledger
import Data.Either
import Data.Map qualified as Map
import Data.Maybe
import Data.Maybe.Strict
import Data.Sequence.Strict qualified as Seq
import Data.Set qualified as Set
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
import Data.Word

import Test.QuickCheck.ContractModel.Internal
import Test.QuickCheck.ContractModel.Internal.ChainIndex
import Test.QuickCheck.ContractModel.Internal.Common

import Test.QuickCheck

import Text.PrettyPrint hiding ((<>))

-- TODO: for some reason the plutus-apps emulator fails if you use inline datums - so
-- all such transactions fail to validate.

-- TODO: Fix the monitoring uglyness:
-- * implement tabulate, classify, etc. with monitor and counterexample with monitorLocal
-- * re-export all of quickcheck without the monitoring functions to avoid name clashes in
--   client code

type Target = PaymentCredential

data Output = Output { outputTxOut :: TxOut CtxTx Era
                     , outputIx    :: TxIx }
  deriving Show

targetToAddressAny :: Target -> AddressAny
targetToAddressAny t =
  AddressShelley $ makeShelleyAddress (Testnet $ NetworkMagic 1) t NoStakeAddress

type Datum    = TxOutDatum CtxTx Era
type Redeemer = ScriptData

data TxMod where

  RemoveInput    :: TxIn
                 -> TxMod

  RemoveOutput   :: TxIx
                 -> TxMod

  ChangeOutput :: TxIx -> Maybe AddressAny -> Maybe Value -> Maybe Datum -> TxMod
  ChangeInput  :: TxIn -> Maybe AddressAny -> Maybe Value -> TxMod

  ChangeScriptInput :: TxIn
                    -> Maybe Value
                    -> Maybe Datum
                    -> Maybe Redeemer
                    -> TxMod

  AddOutput :: AddressAny -> Value -> Datum -> TxMod
  AddInput  :: AddressAny -> Value -> Datum -> TxMod

  AddScriptInput :: ScriptInEra Era
                 -> Value
                 -> Datum
                 -> Redeemer
                 -> TxMod


  AddSimpleScriptInput :: SimpleScript SimpleScriptV2
                       -> Value
                       -> TxMod
  deriving (Show)

recomputeScriptData :: Maybe Word64 -- Index to remove
                    -> (Word64 -> Word64)
                    -> TxBodyScriptData Era
                    -> TxBodyScriptData Era
recomputeScriptData _ _ TxBodyNoScriptData = TxBodyNoScriptData
recomputeScriptData i f (TxBodyScriptData era dats (Ledger.Redeemers rdmrs)) =
  TxBodyScriptData era dats
    (Ledger.Redeemers $ Map.mapKeys updatePtr $ Map.filterWithKey idxFilter rdmrs)
  where updatePtr (Ledger.RdmrPtr tag idx) = Ledger.RdmrPtr tag (f idx)
        idxFilter (Ledger.RdmrPtr _ idx) _ = Just idx /= i

applyTxMod :: Tx Era -> UTxO Era -> TxMod -> (Tx Era, UTxO Era)

applyTxMod tx utxos (RemoveInput i) =
    (Tx (ShelleyTxBody era body{Ledger.inputs = inputs'} scripts scriptData' auxData validity) wits, utxos)
  where
    Tx (ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx
    inputs' = Set.delete (toShelleyTxIn i) inputs
    SJust idx = Ledger.indexOf (toShelleyTxIn i) inputs
    idxUpdate idx'
      | idx' > idx = idx' - 1
      | otherwise  = idx'
    scriptData' = recomputeScriptData (Just idx) idxUpdate scriptData

applyTxMod tx utxos (RemoveOutput (TxIx i)) =
    (Tx (ShelleyTxBody era body{Ledger.outputs = outputs'} scripts scriptData auxData validity) wits, utxos)
  where
    Tx (ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx
    outputs' = case Seq.splitAt (fromIntegral i) outputs of
                 (before, _ Seq.:<| after) -> before <> after
                 (_, Seq.Empty)            -> error $ "RemoveOutput: Can't remove index " ++ show i ++ " from "
                                                   ++ show (Seq.length outputs) ++ " outputs"

applyTxMod tx utxos (AddOutput addr value datum) =
    (Tx (ShelleyTxBody era body{Ledger.outputs = outputs'} scripts scriptData' auxData validity) wits, utxos)
  where
    Tx (ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx
    outputs' = outputs Seq.:|> CBOR.mkSized out
    out = toShelleyTxOut shelleyBasedEra (makeTxOut addr value datum ReferenceScriptNone)
    scriptData' = case datum of
      TxOutDatumNone       -> scriptData
      TxOutDatumHash{}     -> scriptData
      TxOutDatumInTx _ d   -> addDatum (toAlonzoData d) scriptData
      TxOutDatumInline _ d -> addDatum (toAlonzoData d) scriptData

applyTxMod tx utxos (AddInput addr value datum) =
    ( Tx (ShelleyTxBody era body{Ledger.inputs = inputs'} scripts scriptData'' auxData validity) wits
    , utxos' )
  where
    Tx (ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx

    txIn    = TxIn dummyTxId (TxIx txIx)
    txIx    = maximum $ 0 : map (+ 1) [ ix | TxIn txId (TxIx ix) <- Map.keys $ unUTxO utxos, txId == dummyTxId ]
    input   = toShelleyTxIn txIn
    inputs' = Set.insert input inputs
    SJust idx = Ledger.indexOf input inputs'

    txOut   = makeTxOut addr value datum ReferenceScriptNone
    utxos'  = UTxO . Map.insert txIn txOut . unUTxO $ utxos

    idxUpdate idx'
      | idx' >= idx = idx' + 1
      | otherwise   = idx'

    scriptData'' = case datum of
      TxOutDatumNone       -> scriptData'
      TxOutDatumHash{}     -> scriptData'
      TxOutDatumInTx _ d   -> addDatum (toAlonzoData d) scriptData'
      TxOutDatumInline _ d -> addDatum (toAlonzoData d) scriptData'

    scriptData' = recomputeScriptData Nothing idxUpdate scriptData

applyTxMod tx utxos (AddScriptInput script value datum redeemer) =
    ( Tx (ShelleyTxBody era body{Ledger.inputs = inputs'} scripts' scriptData' auxData validity) wits
    , utxos' )
  where
    Tx (ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx

    txIx   = maximum $ 0 : map (+ 1) [ ix | TxIn txId (TxIx ix) <- Map.keys $ unUTxO utxos, txId == dummyTxId ]
    txIn   = TxIn dummyTxId (TxIx txIx)
    input  = toShelleyTxIn txIn
    inputs' = Set.insert input inputs

    txOut  = makeTxOut addr value datum ReferenceScriptNone
    utxos' = UTxO . Map.insert txIn txOut . unUTxO $ utxos

    newScript = toShelleyScript @Era script
    scripts'  = scripts ++ [newScript]

    SJust idx = Ledger.indexOf input inputs'
    idxUpdate idx'
      | idx' >= idx = idx' + 1
      | otherwise   = idx'

    datum' = case datum of
      TxOutDatumNone       -> error "Bad test!"
      TxOutDatumHash{}     -> error "Bad test!"
      TxOutDatumInTx _ d   -> toAlonzoData d
      TxOutDatumInline _ d -> toAlonzoData d

    scriptData' = addScriptData idx datum' (toAlonzoData redeemer, toAlonzoExUnits $ ExecutionUnits 0 0)
                $ recomputeScriptData Nothing idxUpdate scriptData

    hash = case script of
             ScriptInEra _ scr -> hashScript scr
    addr = targetToAddressAny $ PaymentCredentialByScript hash


applyTxMod tx utxos (AddSimpleScriptInput script value) =
    ( Tx (ShelleyTxBody era body{Ledger.inputs = inputs'} scripts' scriptData' auxData validity) wits
    , utxos' )
  where
    Tx (ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx

    txIx   = maximum $ 0 : map (+ 1) [ ix | TxIn txId (TxIx ix) <- Map.keys $ unUTxO utxos, txId == dummyTxId ]
    txIn   = TxIn dummyTxId (TxIx txIx)
    input  = toShelleyTxIn txIn
    inputs' = Set.insert input inputs

    txOut  = makeTxOut addr value TxOutDatumNone ReferenceScriptNone
    utxos' = UTxO . Map.insert txIn txOut . unUTxO $ utxos

    scriptInEra = ScriptInEra SimpleScriptV2InBabbage
                  (SimpleScript SimpleScriptV2 script)
    newScript = toShelleyScript @Era scriptInEra
    scripts'  = scripts ++ [newScript]

    SJust idx = Ledger.indexOf input inputs'
    idxUpdate idx'
      | idx' >= idx = idx' + 1
      | otherwise   = idx'

    scriptData' = recomputeScriptData Nothing idxUpdate scriptData

    addr = targetToAddressAny $ PaymentCredentialByScript $ hashScript (SimpleScript SimpleScriptV2 script)

applyTxMod tx utxos (ChangeOutput ix maddr mvalue mdatum) =
    (Tx (ShelleyTxBody era body{Ledger.outputs = outputs'} scripts scriptData' auxData validity) wits, utxos)
  where
    TxIx (fromIntegral -> idx) = ix
    Tx bdy@(ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx
    TxBody (TxBodyContent{txOuts=txOuts}) = bdy
    TxOut (AddressInEra _ (toAddressAny -> addr)) (txOutValueToValue -> value) datum rscript = txOuts !! idx
    (outputsStart, _ Seq.:<| outputsEnd) = Seq.splitAt idx outputs
    outputs' = outputsStart Seq.>< (CBOR.mkSized out Seq.:<| outputsEnd)
    out = toShelleyTxOut shelleyBasedEra (makeTxOut (fromMaybe addr maddr)
                                                    (fromMaybe value mvalue)
                                                    (fromMaybe datum mdatum)
                                                    rscript)
    scriptData' = case mdatum of
      Nothing -> scriptData
      Just d -> case d of
        TxOutDatumNone       -> scriptData
        TxOutDatumHash{}     -> scriptData
        TxOutDatumInTx _ d   -> addDatum (toAlonzoData d) scriptData
        TxOutDatumInline _ d -> addDatum (toAlonzoData d) scriptData


applyTxMod tx utxos (ChangeInput txIn maddr mvalue) =
    (tx , utxos')
  where
    (addr, value, datum, rscript) = case Map.lookup txIn $ unUTxO utxos of
      Just (TxOut (AddressInEra _ (toAddressAny -> addr)) (txOutValueToValue -> value) datum rscript) ->
        (addr, value, datum, rscript)
      Nothing -> error $ "Index " ++ show txIn ++ " doesn't exist."


    txOut = TxOut (anyAddressInShelleyBasedEra (fromMaybe addr maddr))
                  (TxOutValue MultiAssetInBabbageEra $ fromMaybe value mvalue)
                  datum
                  rscript
    utxos' = UTxO . Map.insert txIn txOut . unUTxO $ utxos

applyTxMod tx utxos (ChangeScriptInput txIn mvalue mdatum mredeemer) =
    (Tx (ShelleyTxBody era body scripts scriptData' auxData validity) wits, utxos')
  where
    Tx (ShelleyTxBody era body@Ledger.TxBody{..} scripts scriptData auxData validity) wits = tx
    (addr, value, utxoDatum, rscript) = case Map.lookup txIn $ unUTxO utxos of
      Just (TxOut addr (txOutValueToValue -> value) utxoDatum rscript) ->
        (addr, value, utxoDatum, rscript)
      Nothing -> error $ "The index " ++ show txIn ++ " doesn't exist."


    (datum, (redeemer, exunits)) = case scriptData of
      TxBodyNoScriptData -> error "No script data available"
      TxBodyScriptData _ (Ledger.TxDats dats) (Ledger.Redeemers rdmrs) ->
        (fromJust $ Map.lookup utxoDatumHash dats,
         fromJust $ Map.lookup (Ledger.RdmrPtr Ledger.Spend idx) rdmrs)

    utxoDatumHash = case utxoDatum of
      TxOutDatumNone       -> error "No existing datum"
      TxOutDatumInline _ d -> coerce $ hashScriptData d
      TxOutDatumHash _ h   -> coerce h

    adatum = case mdatum of
      Just (TxOutDatumNone)       -> error "Bad test!"
      Just (TxOutDatumHash{})     -> error "Bad test!"
      Just (TxOutDatumInTx _ d)   -> toAlonzoData d
      Just (TxOutDatumInline _ d) -> toAlonzoData d
      Nothing                     -> datum

    txOut = TxOut addr
                  (TxOutValue MultiAssetInBabbageEra $ fromMaybe value mvalue)
                  (fromMaybe utxoDatum $ toCtxUTxO <$> mdatum)
                  rscript

    utxos' = UTxO . Map.insert txIn txOut . unUTxO $ utxos

    idx = case Ledger.indexOf (toShelleyTxIn txIn) inputs of
      SJust idx -> idx
      _         -> error "The impossible happened!"

    scriptData' = addScriptData idx adatum
                                    (fromMaybe redeemer (toAlonzoData <$> mredeemer), exunits)
                                    scriptData

    toCtxUTxO d = case d of
      TxOutDatumNone        -> TxOutDatumNone
      TxOutDatumHash s h    -> TxOutDatumHash s h
      TxOutDatumInTx s d    -> TxOutDatumHash s (hashScriptData d)
      TxOutDatumInline s sd -> TxOutDatumInline s sd

emptyTxBodyScriptData :: TxBodyScriptData Era
emptyTxBodyScriptData = TxBodyScriptData ScriptDataInBabbageEra (Ledger.TxDats mempty) (Ledger.Redeemers mempty)

addScriptData :: Word64
              -> Ledger.Data (ShelleyLedgerEra Era)
              -> (Ledger.Data (ShelleyLedgerEra Era), Ledger.ExUnits)
              -> TxBodyScriptData Era
              -> TxBodyScriptData Era
addScriptData ix dat rdmr TxBodyNoScriptData = addScriptData ix dat rdmr emptyTxBodyScriptData
addScriptData ix dat rdmr (TxBodyScriptData era (Ledger.TxDats dats) (Ledger.Redeemers rdmrs)) =
  TxBodyScriptData era (Ledger.TxDats $ Map.insert (Ledger.hashData dat) dat dats)
                       (Ledger.Redeemers $ Map.insert (Ledger.RdmrPtr Ledger.Spend ix) rdmr rdmrs)

addDatum :: Ledger.Data (ShelleyLedgerEra Era)
         -> TxBodyScriptData Era
         -> TxBodyScriptData Era
addDatum dat TxBodyNoScriptData = addDatum dat emptyTxBodyScriptData
addDatum dat (TxBodyScriptData era (Ledger.TxDats dats) rdmrs) =
  TxBodyScriptData era (Ledger.TxDats $ Map.insert (Ledger.hashData dat) dat dats)
                       rdmrs

-- | Used for new inputs.
dummyTxId :: TxId
dummyTxId =
  fromShelleyTxId
  $ txid @LedgerEra
  $ Ledger.TxBody @LedgerEra
      mempty
      mempty
      mempty
      Seq.empty
      SNothing
      SNothing
      Seq.empty
      (Wdrl mempty)
      mempty
      (ValidityInterval SNothing SNothing)
      SNothing
      mempty
      mempty
      SNothing
      SNothing
      SNothing

makeTxOut :: AddressAny -> Value -> Datum -> ReferenceScript Era -> TxOut CtxUTxO Era
makeTxOut addr value datum refScript =
  toCtxUTxOTxOut $ TxOut (anyAddressInShelleyBasedEra addr)
                         (TxOutValue MultiAssetInBabbageEra value)
                         datum
                         refScript

applyTxModifier :: Tx Era -> UTxO Era -> TxModifier -> (Tx Era, UTxO Era)
applyTxModifier = curry $ foldl (uncurry applyTxMod)

type TxModifier = [TxMod]

prettyUTxO :: UTxO Era -> Doc
prettyUTxO (UTxO utxo) =
  hang "UTxO" 2 $ vcat [ (prettyIn i <> ":") <+> prettyTxOut o | (i, o) <- Map.toList utxo ]

prettyIn :: TxIn -> Doc
prettyIn (TxIn hash ix) =
  text (take 7 $ drop 1 $ show hash) <> brackets (prettyIx ix)

prettyTxOut :: TxOut CtxUTxO Era -> Doc
prettyTxOut (TxOut (AddressInEra _ addr) value datum _) =
  "TxOut" <+> vcat [ prettyAddr (toAddressAny addr)
                   , prettyValue (txOutValueToValue value)
                   , prettyDatum datum'
                   ]
  where
    datum' = case datum of
      TxOutDatumNone        -> TxOutDatumNone
      TxOutDatumHash s h    -> TxOutDatumHash s h
      TxOutDatumInline s sd -> TxOutDatumInline s sd


prettyTxOutTx :: TxOut CtxTx Era -> Doc
prettyTxOutTx (TxOut (AddressInEra _ addr) value datum _) =
  "TxOut" <+> vcat [ prettyAddr (toAddressAny addr)
                   , prettyValue (txOutValueToValue value)
                   , prettyDatum datum
                   ]

prettyAddr :: AddressAny -> Doc
prettyAddr (AddressByron (ByronAddress a)) = text $ show a
prettyAddr (AddressShelley (ShelleyAddress _ c _)) =
  case fromShelleyPaymentCredential c of
    PaymentCredentialByKey h    -> "Key@" <> text (take 7 $ drop 1 $ show h)
    PaymentCredentialByScript h -> "Script@" <> text (take 7 $ drop 1 $ show h)

prettyIx :: TxIx -> Doc
prettyIx (TxIx txIx) = text $ show txIx

prettyValue :: Value -> Doc
prettyValue value =
  braces $ sep $ punctuate "," [ (prettyAssetId assetId <> ":") <+> text (show num)
                               | (assetId, num) <- valueToList value ]

prettyAssetId :: AssetId -> Doc
prettyAssetId AdaAssetId = "lovelace"
prettyAssetId (AssetId hash name) = prettyHash hash <> "." <> prettyName name
  where
    prettyName name = if length (show name) < 10
                      then text (show name)
                      else text (take 9 (show name) ++ "...\"")

prettyHash :: Show a => a -> Doc
prettyHash = text . take 7 . drop 1 . show

prettyDatum :: TxOutDatum CtxTx Era -> Doc
prettyDatum TxOutDatumNone         = empty
prettyDatum (TxOutDatumHash _ h)   = prettyHash h
prettyDatum (TxOutDatumInline _ d) = prettyScriptData d
prettyDatum (TxOutDatumInTx _ d)   = prettyScriptData d

prettyTx :: Tx Era -> Doc
prettyTx (Tx (TxBody (TxBodyContent{..})) wits) =
  "Tx" <+> vcat [ "Inputs:" <+> vcat (map (prettyIn . fst) txIns)
                , "Outputs:" <+> vcat (map prettyTxOutTx txOuts)
                ] -- TODO: validity interval
                  --       minting
                  --       signatories
                  --       redeemers

prettyTxModifier :: TxModifier -> Doc
prettyTxModifier txmod = vcat [prettyMod mod | mod <- txmod]
  where
    prettyScript = parens . text . show

    prettySimpleScript = parens . text . show

    prettyMaybe f Nothing  = "Nothing"
    prettyMaybe f (Just a) = "(Just $ " <> f a <> ")"

    prettyMod (RemoveInput txIn) =
      "RemoveInput" <+> prettyIn txIn

    prettyMod (RemoveOutput ix) =
      "RemoveOutput" <+> prettyIx ix

    prettyMod (ChangeOutput ix maddr mvalue mdatum) =
      "ChangeOutput" <+> sep [ prettyIx ix
                             , prettyMaybe prettyAddr maddr
                             , prettyMaybe prettyValue mvalue
                             , prettyMaybe prettyDatum mdatum
                             ]

    prettyMod (ChangeInput txIn maddr mvalue) =
      "ChangeInput" <+> sep [ prettyIn txIn
                            , prettyMaybe prettyAddr maddr
                            , prettyMaybe prettyValue mvalue
                            ]

    prettyMod (ChangeScriptInput txIn mvalue mdatum mrdmr) =
      "ChangeScriptInput" <+> sep [ prettyIn txIn
                                  , prettyMaybe prettyValue mvalue
                                  , prettyMaybe prettyDatum mdatum
                                  , prettyMaybe prettyScriptData mrdmr
                                  ]

    prettyMod (AddOutput addr value datum) =
      "AddOutput" <+> sep [ prettyAddr addr
                          , prettyValue value
                          , prettyDatum datum
                          ]

    prettyMod (AddInput addr value datum) =
      "AddInput" <+> sep [ prettyAddr addr
                         , prettyValue value
                         , prettyDatum datum
                         ]

    prettyMod (AddScriptInput script value datum redeemer) =
      "AddScriptInput" <+> sep [ prettyScript script
                               , prettyValue value
                               , prettyDatum datum
                               , prettyScriptData redeemer
                               ]

    prettyMod (AddSimpleScriptInput script value) =
      "AddScriptInput" <+> sep [ prettySimpleScript script
                               , prettyValue value
                               ]

prettyScriptData :: ScriptData -> Doc
prettyScriptData (ScriptDataConstructor i args) = "Con" <> text (show i) <> parens (fsep . punctuate "," $ map prettyScriptData args)
prettyScriptData (ScriptDataMap map) = braces . fsep . punctuate "," $
  [ (prettyScriptData k <> ":") <+> prettyScriptData v | (k, v) <- map ]
prettyScriptData (ScriptDataList list) = brackets . fsep . punctuate "," $
  map prettyScriptData list
prettyScriptData (ScriptDataNumber n) = text (show n)
prettyScriptData (ScriptDataBytes bs) = text (show bs)

data ThreatModelEnv = ThreatModelEnv
  { currentTx    :: Tx Era
  , currentUTxOs :: UTxO Era
  , pparams      :: ProtocolParameters
  } deriving Show

-- TODO: transactions can fail for different reasons. Sometimes they fail with
-- a "translation error". Translation errors should probably be treated as test
-- failures not as validation failing - it's after all not validation failing!
data ValidityReport = ValidityReport
  { valid  :: Bool
  , errors :: [String]
  } deriving (Ord, Eq, Show)


data ThreatModel a where
  Validate     :: TxModifier
               -> (ValidityReport -> ThreatModel a)
               -> ThreatModel a

  Generate     :: Show a
               => Gen a
               -> (a -> [a])
               -> (a -> ThreatModel b)
               -> ThreatModel b

  GetCtx       :: (ThreatModelEnv -> ThreatModel a) -> ThreatModel a

  Skip         :: ThreatModel a

  Fail         :: String
               -> ThreatModel a

  Monitor      :: (Property -> Property)
               -> ThreatModel a
               -> ThreatModel a


  MonitorLocal :: (Property -> Property)
               -> ThreatModel a
               -> ThreatModel a

  Done         :: a
               -> ThreatModel a

instance Functor ThreatModel where
  fmap = liftM

instance Applicative ThreatModel where
  pure  = Done
  (<*>) = ap

instance Monad ThreatModel where
  Validate tx cont      >>= k = Validate tx (cont >=> k)
  Skip                  >>= _ = Skip
  Fail err              >>= _ = Fail err
  Generate gen shr cont >>= k = Generate gen shr (cont >=> k)
  GetCtx cont           >>= k = GetCtx (cont >=> k)
  Monitor m cont        >>= k = Monitor m (cont >>= k)
  MonitorLocal m cont   >>= k = MonitorLocal m (cont >>= k)
  Done a                >>= k = k a

instance MonadFail ThreatModel where
  fail = Fail

restrictUTxO :: Tx Era -> UTxO Era -> UTxO Era
restrictUTxO (Tx (TxBody TxBodyContent{..}) _) (UTxO utxo) =
  UTxO $ Map.filterWithKey (\ k _ -> k `elem` map fst txIns) utxo


runThreatModel :: ThreatModel a -> [ThreatModelEnv] -> Property
runThreatModel = go False
  where go b model [] = b ==> property True
        go b model (env : envs) = interp ( counterexample (show $ prettyTx $ currentTx env)
                                         . counterexample (show $ prettyUTxO
                                                                $ restrictUTxO (currentTx env)
                                                                $ currentUTxOs env))
                                         model
          where
            interp mon = \ case
              Validate mods k    -> interp mon
                                  $ k
                                  $ uncurry (validateTx $ pparams env)
                                  $ applyTxModifier (currentTx env) (currentUTxOs env) mods
              Generate gen shr k -> forAllShrinkBlind gen shr
                                  $ interp mon . k
              GetCtx k           -> interp mon
                                  $ k env
              Skip               -> go b model envs
              Fail err           -> mon $ counterexample err False
              Monitor m k        -> m $ interp mon k
              MonitorLocal m k   -> interp (m . mon) k
              Done{}             -> go True model envs

-- NOTE: this function ignores the execution units associated with
-- the scripts in the Tx. That way we don't have to care about computing
-- the right values in the threat model (as this is not our main concern here).
--
-- This also means that if we were to want to deal with execution units in the threat
-- modelling framework we would need to be a bit careful and figure out some abstractions
-- that make it make sense (and check the budgets here).
--
-- Stolen from Hydra
validateTx :: ProtocolParameters -> Tx Era -> UTxO Era -> ValidityReport
validateTx pparams tx utxos = case result of
  Left e -> ValidityReport False [show e]
  Right report -> ValidityReport (all isRight (Map.elems report))
                                 [show e | Left e <- Map.elems report]
  where
    result = evaluateTransactionExecutionUnits
                BabbageEraInCardanoMode
                systemStart
                eraHistory
                pparams
                utxos
                (getTxBody tx)
    eraHistory :: EraHistory CardanoMode
    eraHistory = EraHistory CardanoMode (mkInterpreter summary)

    summary :: Summary (CardanoEras StandardCrypto)
    summary =
      Summary . NonEmptyOne $
        EraSummary
          { eraStart = initBound
          , eraEnd = EraUnbounded
          , eraParams =
              EraParams
                { eraEpochSize = epochSize
                , eraSlotLength = slotLength
                , eraSafeZone = UnsafeIndefiniteSafeZone
                }
          }

    epochSize :: EpochSize
    epochSize = EpochSize 100

    slotLength :: SlotLength
    slotLength = mkSlotLength 1

    systemStart :: SystemStart
    systemStart = SystemStart $ posixSecondsToUTCTime 0

validate :: TxModifier -> ThreatModel ValidityReport
validate tx = Validate tx pure

shouldValidate :: TxModifier -> ThreatModel ()
shouldValidate tx = do
  validReport <- validate tx
  -- TODO: here I think we might want a summary of the reasons
  -- for logging purposes if we are in a precondition
  unless (valid validReport) $ do
    monitorThreatModel $ tabulate "shouldValidate failure reasons" (errors validReport)
    fail $ show $ hang "Expected the following transaction to validate:" 2 (prettyTxModifier tx)

shouldNotValidate :: TxModifier -> ThreatModel ()
shouldNotValidate tx = do
  validReport <- validate tx
  -- TODO: here I think we might want a summary of the reasons
  -- for logging purposes if we are in a precondition
  when (valid validReport) $ do
    fail $ show $ hang "Expected the following transaction not to validate:" 2 (prettyTxModifier tx)

precondition :: ThreatModel a -> ThreatModel a
precondition = \ case
  Skip             -> Skip
  Fail reason      -> Monitor (tabulate "Precondition failed with reason" [reason]) Skip
  Validate tx k    -> Validate tx (precondition . k)
  Generate g s k   -> Generate g s (precondition . k)
  GetCtx k         -> GetCtx (precondition . k)
  Monitor m k      -> Monitor m (precondition k)
  MonitorLocal m k -> MonitorLocal m (precondition k)
  Done a           -> Done a

ensure :: Bool -> ThreatModel ()
ensure False = Skip
ensure True  = pure ()

getCtx :: ThreatModel ThreatModelEnv
getCtx = GetCtx pure

gen :: Show a => Gen a -> (a -> [a]) -> ThreatModel a
gen g s = Generate g s pure

pickSomeInput :: ThreatModel (TxIn, TxOut CtxUTxO Era)
pickSomeInput = do
  ThreatModelEnv tx utxos _ <- getCtx
  idx <- pickAny $ txInputs tx
  case Map.lookup idx $ unUTxO utxos of
    Nothing    -> error "The impossible happened"
    Just txout -> return (idx, txout)

originalTx :: ThreatModel (Tx Era)
originalTx = currentTx <$> getCtx

txOutputs :: Tx Era -> [Output]
txOutputs (Tx (TxBody body) _) = zipWith Output (txOuts body) (map TxIx [0..])

txInputs :: Tx Era -> [TxIn]
txInputs (Tx (TxBody body) _) = map fst $ txIns body

txSigners :: Tx Era -> [Hash PaymentKey]
txSigners (Tx _ wits) = [ toHash wit | ShelleyKeyWitness _ (WitVKey wit _) <- wits ]
  where
    toHash = PaymentKeyHash
           . hashKey
           . coerceKeyRole

pickAny :: Show a => [a] -> ThreatModel a
pickAny xs = do
  ensure (not $ null xs)
  let xs' = zip xs [0..]
  fst <$> gen (elements xs') (\(_, i) -> take i xs')

changeTarget :: output -> Target -> TxModifier
changeTarget output target = []

removeOutput :: Output -> TxModifier
removeOutput output = [RemoveOutput $ outputIx output]

-- TODO: we need to stop people using this with simple scripts - simple
-- scripts are not meant to have plutus validators.
addScriptInput :: ScriptInEra Era -> Value -> Datum -> Redeemer -> TxModifier
addScriptInput script value datum redeemer = [AddScriptInput script value datum redeemer]

addSimpleScriptInput :: SimpleScript SimpleScriptV2 -> Value -> TxModifier
addSimpleScriptInput script value = [AddSimpleScriptInput script value]

addOutput :: AddressAny -> Value -> Datum -> TxModifier
addOutput addr value datum = [AddOutput addr value datum]

anySigner :: ThreatModel (Hash PaymentKey)
anySigner = pickAny . txSigners =<< originalTx

monitorThreatModel :: (Property -> Property) -> ThreatModel ()
monitorThreatModel m = Monitor m (pure ())

monitorLocalThreatModel :: (Property -> Property) -> ThreatModel ()
monitorLocalThreatModel m = MonitorLocal m (pure ())

targetOf :: Output -> AddressAny
targetOf (Output (TxOut (AddressInEra ShelleyAddressInEra{}  addr) _ _ _) _) = AddressShelley addr
targetOf (Output (TxOut (AddressInEra ByronAddressInAnyEra{} addr) _ _ _) _) = AddressByron   addr

valueOf :: Output -> Value
valueOf (Output (TxOut _ val _ _) _) =
  case val of
    TxOutAdaOnly _ v -> lovelaceToValue v
    TxOutValue _ v   -> v

datumOf :: Output -> Datum
datumOf (Output (TxOut _ _ dat _) _) = dat

txOutDatum :: ScriptData -> Datum
txOutDatum d = TxOutDatumInTx ScriptDataInBabbageEra d

toScriptData :: ToData a => a -> ScriptData
toScriptData = fromPlutusData . toData

mkSafeScript :: Hash PaymentKey -> SimpleScript SimpleScriptV2
mkSafeScript h = RequireSignature h

changeValueOf :: Output -> Value -> TxModifier
changeValueOf output val = [ChangeOutput (outputIx output) Nothing (Just val) Nothing]

projectAda :: Value -> Value
projectAda = lovelaceToValue . selectLovelace

doubleSatisfaction :: ThreatModel ()
doubleSatisfaction = do

  signer <- anySigner
  let signerTarget = PaymentCredentialByKey signer
      signerAddr   = targetToAddressAny signerTarget

  outputs <- txOutputs <$> originalTx
  output  <- pickAny $ filter ((/= signerAddr) . targetOf) outputs

  let ada = projectAda $ valueOf output

  -- redirect output to signer: precondition: this should fail
  precondition $ shouldNotValidate $ changeValueOf output (valueOf output <> negateValue ada)
                                  <> addOutput signerAddr ada TxOutDatumNone

  -- add safe script input with protected output, redirect original output to signer
  let safeScript  = mkSafeScript signer -- TODO: this is not the right script!
      uniqueDatum = txOutDatum $ toScriptData ("SuchSecure" :: BuiltinByteString)

      victimTarget = targetOf output

  shouldNotValidate $ addSimpleScriptInput safeScript ada
                   <> addOutput      victimTarget ada uniqueDatum
                   <> changeValueOf  output (valueOf output <> negateValue ada)
                   <> addOutput      signerAddr ada TxOutDatumNone

assertThreatModel :: ProtocolParameters
                  -> ThreatModel a
                  -> ContractModelResult state
                  -> Property
assertThreatModel params m result = runThreatModel m envs
  where
    envs = [ ThreatModelEnv (tx txInState) (utxo $ chainState txInState) params
           | txInState <- transactions $ finalChainIndex result ]

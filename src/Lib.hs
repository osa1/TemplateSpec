{-# LANGUAGE LambdaCase, TupleSections #-}

module Lib where

--------------------------------------------------------------------------------

import           Control.Monad                ((>=>))
import           Data.List                    (foldl', intercalate)
import           Data.Maybe                   (catMaybes, fromMaybe)
import           Data.Typeable                (Typeable)

import qualified Data.Map.Strict              as M

import           Language.Haskell.TH.Quote
import           Language.Haskell.TH.Syntax   as TH

import           Language.Haskell.Exts.Parser
import           Language.Haskell.Exts.Pretty (prettyPrint)
import           Language.Haskell.Exts.Syntax as HSE

--------------------------------------------------------------------------------

-- | State shared between different invocations of Q.
data InstState = InstState
  { _isTemplates :: ![TyDeclTempl]
      -- ^ User defined templates. 'spec' quoter generates these.
  , _isInstances :: !(M.Map [HSE.Type] TH.Name)
      -- ^ Instances we declared so far. 'specInst' generates and uses these.
  , _isUs        :: !Int
      -- ^ Uniques used for type name generation
  } deriving (Show, Typeable)

initInstState :: Q ()
initInstState = putQ (InstState [] M.empty 1)

getInstState :: Q (Maybe InstState)
getInstState = getQ

putInstState :: InstState -> Q ()
putInstState = putQ

--------------------------------------------------------------------------------

data TyDeclTempl
  = TyDeclTempl !HSE.Name ![HSE.Name] ![QualConDecl] ![Deriving]
  deriving (Show, Typeable)

-- | Quoter for declarations.
spec :: QuasiQuoter
spec = QuasiQuoter
    { quoteExp  = qFail
    , quotePat  = qFail
    , quoteType = qFail
    , quoteDec  = decQuoter
    }
  where
    qFail  = const (fail errMsg)
    errMsg = "spec quasi-quoter generates type declarations, " ++
             "try using it in a type declaration context(e.g. top-level)"

decQuoter :: String -> Q [Dec]
decQuoter decStr =
    case parseDecl decStr of
      ParseOk (DataDecl loc DataType [] tyName tyVars cons derivings) ->
        processDecl loc tyName (map removeKind tyVars) cons derivings

      ParseOk unsupported ->
        fail $ unlines
          [ "spec quoter: Unsupported declaration:"
          , prettyPrint unsupported ]

      ParseFailed _ err ->
        fail $ unlines
          [ "spec quoter: Can't parse data type declaration:"
          , decStr
          , "error: " ++ err ]
  where
    removeKind :: TyVarBind -> HSE.Name
    removeKind (KindedVar n _) = n
    removeKind (UnkindedVar n) = n


processDecl :: SrcLoc -> HSE.Name -> [HSE.Name] -> [QualConDecl] -> [Deriving] -> Q [Dec]
processDecl _loc dName tyVars cons derivings = do
    let d = TyDeclTempl dName tyVars cons derivings
    getQ >>= \case
      Nothing -> putQ [d]
      Just st -> putQ (d : st)
    return []

--------------------------------------------------------------------------------

specInst :: QuasiQuoter
specInst = QuasiQuoter
    { quoteExp  = qFail
    , quotePat  = qFail
    , quoteType = tyInstQuoter
    , quoteDec  = tyInstInstQuoter
    }
  where
    qFail  = const (fail errMsg)
    errMsg = "specInst quasi-quoter generates type declerations and types, " ++
             "try using it in a type declaration of type context"

tryParseTyAppStr :: String -> Q [HSE.Type]
tryParseTyAppStr tyStr =
    case parseType tyStr of
      ParseOk (TyApp t1 t2) ->
        return (collectTyAppArgs t1 t2)

      ParseOk unsupported ->
        fail $ unlines
          [ "specInst quoter: Unsupported type:"
          , prettyPrint unsupported ]

      ParseFailed _ err ->
        fail $ unlines
          [ "specInst quoter: Can't parse type:"
          , tyStr
          , "error: " ++ err ]

tyInstQuoter :: String -> Q TH.Type
tyInstQuoter = tryParseTyAppStr >=> processType

collectTyAppArgs :: HSE.Type -> HSE.Type -> [HSE.Type]
collectTyAppArgs (TyApp t1 t2) t3 = collectTyAppArgs t1 t2 ++ [t3]
collectTyAppArgs t1            t2 = [t1, t2]

processType :: [HSE.Type] -> Q TH.Type
processType [_] = fail "processType: Need a type application"
processType []  = fail "processType: Empty argument"

processType ty@(tyCon : args) = do
    getInstState >>= \case
      Nothing -> fail "processType: Template state is not initialized"
      Just (InstState _ insts _) ->
        case M.lookup ty insts of
          Nothing ->
            fail $ "processType: Type used before instantiation: "
                 ++ prettyPrint (foldl' TyApp tyCon args)
          Just thTy -> return (ConT thTy)

tyInstInstQuoter :: String -> Q [Dec]
tyInstInstQuoter = tryParseTyAppStr >=> processTypeInst

-- Here we do the new specialized data type creation.
processTypeInst :: [HSE.Type] -> Q [Dec]
processTypeInst []  = fail "processTypeInst: Empty argument"

processTypeInst (TyVar tyCon : args) =
    getInstState >>= \case
      Nothing -> fail "processTypeInst: Type state is not initialized"
      Just (InstState templs insts us) ->
        case findTemplate tyCon (length args) templs of
          Nothing ->
            fail $ unlines
              [ "processTypeInst: Can't find a template for instantiation."
              , "  tyCon: " ++ prettyPrint tyCon
              , "  args:  " ++ intercalate ", " (map prettyPrint args)
              , "  available templates:"
              , show templs ]

          Just (TyDeclTempl _ args' cons derivings) -> do
            let cons'  = map (substCon (zip args' args)) cons
                us'    = us + 1
                tyName = nameStr tyCon ++ show us
            tyThName <- newName tyName
            -- freshName
            putInstState (InstState templs (M.insert args tyThName insts) us')
            tyArgNames <- catMaybes <$> mapM argName args
            let newDecl = DataD [] tyThName tyArgNames (map translateCon cons') []
                            -- FIXME: deriving part
            return [newDecl]
  where
    argName :: HSE.Type -> Q (Maybe TyVarBndr)
    argName (TyVar name) = Just . PlainTV <$> newName (nameStr name)
    argName _            = return Nothing

processTypeInst _ = fail "processTypeInst: Need a type application"

findTemplate :: HSE.Name -> Int -> [TyDeclTempl] -> Maybe TyDeclTempl
findTemplate _ _ [] = Nothing
findTemplate tyCon arity (templ@(TyDeclTempl name args _ _) : rest)
  | tyCon == name && length args == arity
  = Just templ
  | otherwise
  = findTemplate tyCon arity rest

--------------------------------------------------------------------------------

substCon :: [(HSE.Name, HSE.Type)] -> QualConDecl -> QualConDecl
substCon substs (QualConDecl loc as ctxt con) =
    QualConDecl loc as ctxt (substCon' substs con)

substCon' :: [(HSE.Name, HSE.Type)] -> ConDecl -> ConDecl
substCon' substs (ConDecl conName tys) = ConDecl conName (map (substTy substs) tys)
substCon' _ unsupported = error $ "substCon': Unsupported con: " ++ prettyPrint unsupported

substTy :: [(HSE.Name, HSE.Type)] -> HSE.Type -> HSE.Type
substTy substs ty =
    case ty of
      TyApp ty1 ty2 -> TyApp (substTy substs ty1) (substTy substs ty2)
      TyVar var -> fromMaybe (TyVar var) (lookup var substs)
      TyCon{} -> ty
      TyParen ty' -> TyParen (substTy substs ty')
      unsupported -> error $ "substTy: Unsupported type: " ++ prettyPrint unsupported

nameStr :: HSE.Name -> String
nameStr (Ident str)  = str
nameStr (Symbol str) = str

translateCon :: QualConDecl -> Con
translateCon (QualConDecl _ [] [] con) =
                  -- we don't support existentials and context
    translateCon' con

translateCon unsupported =
    error $ "translateCon: Unsupported constructor: " ++ prettyPrint unsupported

translateCon' :: ConDecl -> Con
translateCon' (ConDecl conName args) =
    NormalC (translateName conName) (map translateTypeS args)
translateCon' unsupported =
    error $ "translateCon': Unsupported con: " ++ prettyPrint unsupported

translateTypeS :: HSE.Type -> (Strict, TH.Type)
translateTypeS (TyBang BangedTy   t) = (IsStrict, translateType t)
translateTypeS (TyBang UnpackedTy t) = (Unpacked, translateType t)
translateTypeS t                     = (NotStrict, translateType t)

translateType :: HSE.Type -> TH.Type
translateType (TyApp t1 t2) = AppT (translateType t1) (translateType t2)
translateType (TyVar var) = VarT (translateName var)
translateType (TyCon (UnQual n)) = ConT (translateName n)
translateType (TyParen t) = translateType t
translateType unsupported =
    error $ "translateType: Unsupported type: " ++ prettyPrint unsupported

translateName :: HSE.Name -> TH.Name
translateName n = TH.Name (OccName (nameStr n)) NameS

--------------------------------------------------------------------------------

someFunc :: IO ()
someFunc = putStrLn "someFunc"

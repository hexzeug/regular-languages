import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Text.ParserCombinators.ReadP (ReadP, char, option, readP_to_S, satisfy)
import Control.Applicative ((<|>))
import Control.Monad.State (State, MonadState(state, get, put), runState)
import Data.Unique (Unique, newUnique)
import Control.Arrow ((&&&))
import Data.Maybe (fromMaybe, mapMaybe)
import Data.List (sort, groupBy, intercalate)
import Data.Function (on)
import Control.Monad (when)
import System.IO (hFlush, stdout)

-- RegularExpressions

data RE a =
    Union (RE a) (RE a) |
    Concat (RE a) (RE a) |
    Kleene (RE a) |
    Sym a |
    Lambda |
    Empty
    deriving (Show, Eq)

instance Read (RE Char) where
    readsPrec :: Int -> ReadS (RE Char)
    readsPrec _ = readP_to_S parseRE

parseRE :: ReadP (RE Char)
parseRE = parseUnion

parseUnion :: ReadP (RE Char)
parseUnion = do
    left <- parseConcat
    rest <- option Nothing (Just <$> (char '+' *> parseUnion))
    case rest of
        Nothing -> return left
        Just right -> return (Union left right)

parseConcat :: ReadP (RE Char)
parseConcat = do
    left <- parseKleene
    rest <- option Nothing (Just <$> parseConcat)
    case rest of
        Nothing -> return left
        Just right -> return (Concat left right)

parseKleene :: ReadP (RE Char)
parseKleene = do
    atom <- parseAtom
    kleene <- option False (True <$ char '*')
    return (if kleene then Kleene atom else atom)

parseAtom :: ReadP (RE Char)
parseAtom = parseSymbol <|> parseLambda <|> parseParens

parseSymbol :: ReadP (RE Char)
parseSymbol = Sym <$> satisfy (`notElem` "+*()/")

parseLambda :: ReadP (RE Char)
parseLambda = Lambda <$ char '/'

parseParens :: ReadP (RE Char)
parseParens = char '(' *> parseRE <* char ')'

-- Finite Automata

newtype IntState = IntState Integer
    deriving (Show, Eq, Ord)

class DeltaMap m where
    deltaUnion :: m -> m -> m

type DDeltaMap q a = (Map.Map (q, a) q)

instance (Ord a, Ord q) => DeltaMap (DDeltaMap q a) where
    deltaUnion :: DDeltaMap q a -> DDeltaMap q a -> DDeltaMap q a
    deltaUnion = Map.unionWith equalOrError
        where
            equalOrError a b
                | a == b = a
                | otherwise = error "Non-deterministic (duplicate) delta step"

type NDeltaMap q a = (Map.Map (q, Maybe a) (Set.Set q))

instance (Ord a, Ord q) => DeltaMap (NDeltaMap q a) where
    deltaUnion :: NDeltaMap q a -> NDeltaMap q a -> NDeltaMap q a
    deltaUnion = Map.unionWith Set.union

deltaSingleton :: (a, b) -> Map.Map a b
deltaSingleton = uncurry Map.singleton

deltaInsert :: (Ord a, Ord b) => (a, b) -> Map.Map a b -> Map.Map a b
deltaInsert = uncurry Map.insert

nondetStep :: Ord a => q -> a -> q -> ((q, Maybe a), Set.Set q)
nondetStep q0 a q1 = ((q0, Just a), Set.singleton q1)

lambdaStep :: Ord a => q -> q -> ((q, Maybe a), Set.Set q)
lambdaStep q0 q1 = ((q0, Nothing), Set.singleton q1)

lambdaSteps :: (Ord q, Ord a) => [(q, q)] -> NDeltaMap q a
lambdaSteps = Map.fromListWith Set.union . map (uncurry lambdaStep)

data CompleteDFA q a = CompleteDFA (Set.Set q) (Set.Set a) q (Set.Set q) (DDeltaMap q a)
    deriving (Show)

data ComposableNFA q a = ComposableNFA (Set.Set q) (Set.Set a) q q (NDeltaMap q a)
    deriving (Show)

-- LaTeX

class LaTeX a where
    latex :: a -> String

instance LaTeX (RE Char) where
    latex :: RE Char -> String
    latex (Union a b) = latex a ++ "+" ++ latex b
    latex (Concat a b) = latex' a ++ latex' b
        where
            parens (Union _ _) = True
            parens _ = False
            latex' a = if parens a then "\\left(" ++ latex a ++ "\\right)" else latex a
    latex (Kleene a) = latex' a ++ "^*"
        where
            parens (Sym _) = False
            parens _ = True
            latex' a = if parens a then "\\left(" ++ latex a ++ "\\right)" else latex a
    latex (Sym c) = c : ""
    latex Lambda = "\\Lambda"
    latex Empty = "\\emptyset"

-- Graphviz

class Graphviz f where
    graphviz :: f -> String
    graphviz f =
        let
            (qs, IntState q0, isA, ts) = normalize f
        in
            "digraph NFA {\n\
            \  rankdir=LR;\n\
            \  node [shape=circle];\n\n\
            \  start [shape=point];\n\
            \" ++ unlines (map (state isA) qs) ++ "\n\

            \  start -> q" ++ show q0 ++ ";\n\
            \" ++ unlines (map transition ts) ++ "\

            \}"
        where
            state isA (IntState q) =
                let
                    optShape = if isA (IntState q) then "shape=doublecircle, " else ""
                in
                    "  q" ++ show q ++ " [" ++ optShape ++ "label=\"q" ++ show q ++ "\"];"
            transition (IntState q1, IntState q2, as) =
                "  q" ++ show q1 ++ " -> q" ++ show q2 ++ " [label=<" ++ intercalate "," (map symbol as) ++ ">];"
            symbol (Just c) = c : ""
            symbol Nothing = "&Lambda;"

    normalize :: f -> ([IntState], IntState, IntState -> Bool, [(IntState, IntState, [Maybe Char])])

instance Graphviz (ComposableNFA IntState Char) where
    normalize :: ComposableNFA IntState Char -> ([IntState], IntState, IntState -> Bool, [(IntState, IntState, [Maybe Char])])
    normalize (ComposableNFA qq s q0 qa nm) =
        (
            Set.toList qq,
            q0,
            (==qa),
            transitions nm
        )
        where
            transitions :: NDeltaMap IntState Char -> [(IntState, IntState, [Maybe Char])]
            transitions = map unw . groupBy ((==) `on` fst) . sort . concatMap sep . Map.toList
            sep ((q1, a), qs) = map ((,a) . (q1,)) (Set.toList qs)
            unw (((q1, q2), a) : ls) = (q1, q2, a : map snd ls)

instance Graphviz (CompleteDFA IntState Char) where
    normalize :: CompleteDFA IntState Char -> ([IntState], IntState, IntState -> Bool, [(IntState, IntState, [Maybe Char])])
    normalize (CompleteDFA qq s q0 aa dm) =
        (
            Set.toList qq,
            q0,
            flip Set.member aa,
            transitions dm
        )
        where
            transitions = map unw . groupBy ((==) `on` fst) . sort . map prp . Map.toList
            prp ((q1, a), q2) = ((q1, q2), Just a)
            unw (((q1, q2), a) : ls) = (q1, q2, a : map snd ls)

-- Conversion

class Conversion a b where
    convert :: a -> b

-- RE -> NFA

type IntStateM = State Integer

newIntState :: IntStateM IntState
newIntState = state (IntState &&& (+1))

runIntStateM :: IntStateM a -> a
runIntStateM = fst . flip runState 0

instance Ord a => Conversion (RE a) (ComposableNFA IntState a) where
    convert :: RE a -> ComposableNFA IntState a
    convert re = runIntStateM (convert' re)
        where
            convert' (Sym a) = do
                q0 <- newIntState
                q1 <- newIntState
                let qq = Set.fromList [q0, q1]
                let s = Set.singleton a
                let m = deltaSingleton (nondetStep q0 a q1)
                return $ ComposableNFA qq s q0 q1 m
            convert' Lambda = do
                q0 <- newIntState
                q1 <- newIntState
                let qq = Set.fromList [q0, q1]
                let s = Set.empty
                let m = deltaSingleton (lambdaStep q0 q1)
                return $ ComposableNFA qq s q0 q1 m
            convert' (Concat e1 e2) = do
                ComposableNFA qq1 s1 q0 q1 m1 <- convert' e1
                ComposableNFA qq2 s2 q2 q3 m2 <- convert' e2
                let qq = qq1 `Set.union` qq2
                let s = s1 `Set.union` s2
                let m = deltaInsert (lambdaStep q1 q2) (m1 `deltaUnion` m2)
                return $ ComposableNFA qq s q0 q3 m
            convert' (Union e1 e2) = do
                q0 <- newIntState
                ComposableNFA qq1 s1 q1 q2 m1 <- convert' e1
                ComposableNFA qq2 s2 q3 q4 m2 <- convert' e2
                q5 <- newIntState
                let m0 = lambdaSteps [(q0, q1), (q0, q3), (q2, q5), (q4, q5)]
                let qq = qq1 `Set.union` qq2 `Set.union` Set.fromList [q0, q5]
                let s = s1 `Set.union` s2
                let m = m0 `deltaUnion` m1 `deltaUnion` m2
                return $ ComposableNFA qq s q0 q5 m
            convert' (Kleene e) = do
                q0 <- newIntState
                ComposableNFA qq s q1 q2 m <- convert' e
                q3 <- newIntState
                let qq' = qq `Set.union` Set.fromList [q0, q3]
                let m' = m `deltaUnion` lambdaSteps [(q0, q1), (q1, q3), (q2, q3), (q2, q1)]
                return $ ComposableNFA qq' s q0 q3 m'

-- NFA -> DFA

lambdaClosure :: (Ord a, Ord q) => NDeltaMap q a -> Set.Set q -> Set.Set q
lambdaClosure m qs = lambdaClosure' qs qs
    where
        delta q = fromMaybe Set.empty (Map.lookup (q, Nothing) m)
        lambdaClosure' new closure
            | Set.null new = closure
            | otherwise =
                let
                    closure' = Set.foldr (Set.union . delta) closure new
                in
                    lambdaClosure' (closure' `Set.difference` closure) closure'

bigDelta :: (Ord a, Ord q) => NDeltaMap q a -> Set.Set q -> a -> Set.Set q
bigDelta m q a = lambdaClosure m (Set.foldr (Set.union . delta a) Set.empty q)
    where
        delta a q = fromMaybe Set.empty (Map.lookup (q, Just a) m)

instance (Ord a, Ord q) => Conversion (ComposableNFA q a) (CompleteDFA (Set.Set q) a) where
    convert :: ComposableNFA q a -> CompleteDFA (Set.Set q) a
    convert (ComposableNFA qq s q0 aa nm) =
        let
            q0' = lambdaClosure nm (Set.singleton q0)
            (qq', m') = convert' [q0'] (Set.singleton q0') Map.empty
            aa' = Set.filter (Set.member aa) qq'
        in
            CompleteDFA qq' s q0' aa' m'
        where
            convert' :: [Set.Set q] -> Set.Set (Set.Set q) -> DDeltaMap (Set.Set q) a -> (Set.Set (Set.Set q), DDeltaMap (Set.Set q) a)
            convert' [] qq dm = (qq, dm)
            convert' (q : w) qq dm =
                let
                    as = Set.toList s
                    qs = map (bigDelta nm q) as
                    ml = zip (map (q,) as) qs
                    dm' = dm `deltaUnion` Map.fromList ml
                    qs' = Set.fromList qs `Set.difference` qq
                    w' = Set.toList qs' ++ w
                    qq' = qq `Set.union` qs'
                in
                    convert' w' qq' dm'

-- DFA -> DFA IntState & NFA -> NFA IntState

type Q2IntStateM q = State (Map.Map q IntState, Integer)

getState :: Ord q => q -> Q2IntStateM q IntState
getState q = do
    (m, c) <- get
    case Map.lookup q m of
        Just q' -> return q'
        Nothing -> do
            let q' = IntState c
            put (Map.insert q q' m, c + 1)
            return q'

runQ2IntStateM :: Q2IntStateM q a -> a
runQ2IntStateM = fst . flip runState (Map.empty, 0)

instance (Ord a, Ord q) => Conversion (CompleteDFA q a) (CompleteDFA IntState a) where
    convert :: CompleteDFA q a -> CompleteDFA IntState a
    convert (CompleteDFA qq s q0 aa dm) = runQ2IntStateM convert'
        where
            convert' :: Q2IntStateM q (CompleteDFA IntState a)
            convert' = do
                q0' <- getState q0
                qq' <- Set.fromList <$> mapM getState (Set.toList qq)
                aa' <- Set.fromList <$> mapM getState (Set.toList aa)
                dm' <- Map.fromList <$> mapM getTrans (Map.toList dm)
                return (CompleteDFA qq' s q0' aa' dm')
            getTrans :: ((q, a), q) -> Q2IntStateM q ((IntState, a), IntState)
            getTrans ((q1, a), q2) = do
                q1' <- getState q1
                q2' <- getState q2
                return ((q1', a), q2')

instance (Ord a, Ord q) => Conversion (ComposableNFA q a) (ComposableNFA IntState a) where
    convert :: ComposableNFA q a -> ComposableNFA IntState a
    convert (ComposableNFA qq s q0 qa nm) = runQ2IntStateM convert'
        where
            convert' :: Q2IntStateM q (ComposableNFA IntState a)
            convert' = do
                q0' <- getState q0
                qq' <- Set.fromList <$> mapM getState (Set.toList qq)
                qa' <- getState qa
                nm' <- Map.fromList <$> mapM getTrans (Map.toList nm)
                return (ComposableNFA qq' s q0' qa' nm')
            getTrans :: ((q, Maybe a), Set.Set q) -> Q2IntStateM q ((IntState, Maybe a), Set.Set IntState)
            getTrans ((q, a), qs) = do
                q' <- getState q
                qs' <- Set.fromList <$> mapM getState (Set.toList qs)
                return ((q', a), qs')

-- DFA -> NFA

instance (Ord a, Ord q) => Conversion (CompleteDFA q a) (ComposableNFA (Either IntState q) a) where
    convert :: CompleteDFA q a -> ComposableNFA (Either IntState q) a
    convert (CompleteDFA qq s q0 aa dm) = runIntStateM convert'
        where
            convert' :: IntStateM (ComposableNFA (Either IntState q) a)
            convert' = do
                q0' <- Left <$> newIntState
                qa <- Left <$> newIntState
                let wqq = Set.map Right qq
                let qq' = Set.insert q0' (Set.insert qa wqq)
                let waa = Set.map Right aa
                let wnm = Map.map (Set.singleton . Right) (Map.mapKeys keys dm)
                let nm = lambdaSteps ((q0', Right q0) : map (,qa) (Set.toList waa)) `deltaUnion` wnm
                return (ComposableNFA qq' s q0' qa nm)
            keys (q, a) = (Right q, Just a)

-- DFA -> RE

type MemoM a b = State (Map.Map a b)

memoize :: Ord a => (a -> b) -> a -> MemoM a b b
memoize f a = do
    m <- get
    case Map.lookup a m of
        Just b -> return b
        Nothing -> do
            let b = f a
            put (Map.insert a b m)
            return b

runMemoM :: MemoM a b c -> c
runMemoM = fst . flip runState Map.empty

instance Ord a => Conversion (CompleteDFA IntState a) (RE a) where
    convert :: CompleteDFA IntState a -> RE a
    convert (CompleteDFA qq s (IntState q0) aa dm) =
        let
            lq = fromIntegral (Set.size qq)
            path (IntState qa) = (q0, qa, lq)
            accPaths = map path (Set.toList aa)
        in
            runMemoM (unions <$> mapM (memoize l) accPaths)
        where
            unions [] = Empty
            unions (a : as) = a `union` unions as
            union Empty a = a
            union a Empty = a
            union a b
                | a == b = a
                | otherwise = Union a b
            concat Empty _ = Empty
            concat _ Empty = Empty
            concat Lambda a = a
            concat a Lambda = a
            concat a b = Concat a b
            kleene Empty = Empty
            kleene Lambda = Lambda
            kleene a = Kleene a
            l :: (Integer, Integer, Integer) -> RE a
            l (p, q, 0) =
                let
                    lookup a
                        | Map.lookup (IntState p, a) dm == Just (IntState q) = Just a
                        | otherwise = Nothing
                    steps = unions (map Sym (mapMaybe lookup (Set.toList s)))
                in
                    if p == q then Lambda `union` steps else steps
            l (p, q, k) =
                l (p, q, k - 1) `union` (l (p, k - 1, k - 1) `concat` kleene (l (k - 1, k - 1, k - 1)) `concat` l (k - 1, q, k - 1))

-- Complement

complement :: Ord q => CompleteDFA q a -> CompleteDFA q a
complement (CompleteDFA qq s q0 aa dm) = CompleteDFA qq s q0 (qq `Set.difference` aa) dm

-- Union

class Disjunction a b c where
    union :: a -> b -> c

instance (Ord a, Ord q1, Ord q2) => Disjunction (ComposableNFA q1 a) (ComposableNFA q2 a) (ComposableNFA (Either IntState (Either q1 q2)) a) where
    union (ComposableNFA qq1 s1 q01 qa1 nm1) (ComposableNFA qq2 s2 q02 qa2 nm2)
        | s1 /= s2 = undefined
        | otherwise = runIntStateM union'
        where
            union' = do
                q0 <- Left <$> newIntState
                qa <- Left <$> newIntState
                let wq01 = Right (Left q01)
                let wq02 = Right (Right q02)
                let wqq1 = Set.map (Right . Left) qq1
                let wqq2 = Set.map (Right . Right) qq2
                let qq = Set.insert q0 (Set.insert qa (wqq1 `Set.union` wqq2))
                let wqa1 = Right (Left qa1)
                let wqa2 = Right (Right qa2)
                let wnm1 = Map.map (Set.map (Right . Left)) (Map.mapKeys (first (Right . Left)) nm1)
                let wnm2 = Map.map (Set.map (Right . Right)) (Map.mapKeys (first (Right . Right)) nm2)
                let nm = lambdaSteps [(q0, wq01), (q0, wq02), (wqa1, qa), (wqa2, qa)] `deltaUnion` wnm1 `deltaUnion` wnm2
                return (ComposableNFA qq s1 q0 qa nm)
            first f (a, b) = (f a, b)

-- Useful shortcuts

instance (Ord a, Ord q) => Conversion (ComposableNFA q a) (CompleteDFA IntState a) where
    convert :: ComposableNFA q a -> CompleteDFA IntState a
    convert nfa = convert (convert nfa :: CompleteDFA (Set.Set q) a)

instance (Ord a, Ord q) => Conversion (CompleteDFA q a) (ComposableNFA IntState a) where
    convert :: CompleteDFA q a -> ComposableNFA IntState a
    convert dfa = convert (convert dfa :: ComposableNFA (Either IntState q) a)

instance (Ord a, Ord q1, Ord q2) => Disjunction (ComposableNFA q1 a) (ComposableNFA q2 a) (ComposableNFA IntState a) where
    union :: ComposableNFA q1 a -> ComposableNFA q2 a -> ComposableNFA IntState a
    union nfa1 nfa2 = convert (nfa1 `union` nfa2 :: (ComposableNFA (Either IntState (Either q1 q2)) a))

-- Testing

type R = RE Char
type D = CompleteDFA IntState Char
type N = ComposableNFA IntState Char

vis :: Graphviz f => f -> IO ()
vis x = writeFile "test.dot" (graphviz x)

-- Runtime

ask :: String -> IO ()
ask s = do
    putStr s
    hFlush stdout

main :: IO ()
main = do
    putStrLn ""
    putStrLn "+++ Regular Language Tool +++"
    putStrLn "1) Intersect Regular Expressions"
    putStrLn "2) Exit"
    ask "Choose option: "
    opt <- read <$> getLine :: IO Int
    case opt of
        1 -> do
            main1
            main
        2 -> return ()
        _ -> main

main1 :: IO ()
main1 = do
    putStrLn "Intersect Regular Expressions:"
    ask "Do you want to output intermediate steps? (Y/n): "
    s <- getLine
    let stepOut = case s of
            "n" -> False
            _ -> True
    ask "Number of REs: "
    n <- read <$> getLine :: IO Int
    putStrLn "Enter the REs"
    nfas <- mapM (preprocessRE stepOut) [1..n]
    let nfa' = unions nfas
    when stepOut (writeFile "nfa'.dot" (graphviz nfa'))
    let dfa' = convert nfa' :: D
    when stepOut (writeFile "dfa'.dot" (graphviz dfa'))
    let dfa = complement dfa'
    when stepOut (writeFile "dfa.dot" (graphviz dfa))
    let re = convert dfa :: R
    putStrLn "The intersection is:"
    putStrLn (latex re)
    where
        preprocessRE :: Bool -> Int -> IO N
        preprocessRE stepOut i = do
            ask (show i ++ ": ")
            re <- read <$> getLine :: IO R
            let nfa = convert re :: N
            when stepOut (writeFile ("nfa_" ++ show i ++ ".dot") (graphviz nfa))
            let dfa = convert nfa :: D
            when stepOut (writeFile ("dfa_" ++ show i ++ ".dot") (graphviz dfa))
            let dfa' = complement dfa
            when stepOut (writeFile ("dfa'_" ++ show i ++ ".dot") (graphviz dfa))
            return (convert dfa')
        unions :: [N] -> N
        unions [nfa] = nfa
        unions (nfa : nfas) = nfa `union` unions nfas


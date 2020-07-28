-- Various imports

-- Manipulating Ints on a bit level
import Data.Bits

-- Serialising and saving graphs
import qualified Data.ByteString.Lazy as BS
import System.Directory hiding (readFile)
import Codec.Serialise

-- Parallel Computation
import Control.Parallel.Strategies
import Control.DeepSeq

-- Data structures
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.IntMap.Strict as M

-- Other stuff
import Control.Monad
import Data.Monoid

-- |Represents the number of variables
type NoVars = Int

-- |The type of nodes in our undirected graphs.
type Node = Int

-- |The 'LinGraph' type is the type of undirected graphs which we use
-- to represent linear formulae. This takes the form of a function
-- from two nodes to a boolean which tells us if there is an edge
-- between them.
type LinGraph = Node -> Node -> Bool

-- |'LinGraphC' is a compressed version of the 'LinGraph' type, where
-- the existance of each edge is stored in one bit
type LinGraphC = Int

-- |`calcBit` calculates which bit of a `LinGraphC` corresponds to the
-- edge between two nodes. The ordering here (for 7 variables) is:
-- Bit 0: 0 -- 1
-- Bit 1: 0 -- 2
-- ...
-- Bit 6: 0 -- 6
-- Bit 7: 1 -- 2
-- ...
-- Bit 20: 6 -- 7
-- We always assume that the first node argument is less than the second.
calcBit :: NoVars -- ^ Number of variables in the graphs
        -> Node -- ^ Node a
        -> Node -- ^ Node b
        -> Int -- ^ The bit that determines whether there is an edge between a and b.
calcBit noVars x y
  | x == 0 = y - 1
  | otherwise = noVars - 1 + calcBit (noVars - 1) (x-1) (y-1)

-- |'fromCompressed' converts a compressed graph into a normal graph
fromCompressed :: NoVars -> LinGraphC -> LinGraph
fromCompressed noVars lgc x y
  | x == y = False -- We do not have an edge from x to x
  | x > y = fromCompressed noVars lgc y x -- If x > y we flip the arguments so that x < y
  | y >= noVars = False -- Make sure x and y are bounded correctly
  | x < 0 = False
  | otherwise = testBit lgc $ calcBit noVars x y -- Check if the corresponding bit is 1

-- |'isFromForm' determines if an undirected graph represents a linear formula.
-- This happens when there is no subgraph isomorphic to
-- a -- b
-- |    |
-- c    d
-- To determine this, we check every quadruple of nodes and check all the edges.
-- Lets call a graph valid if it comes from a linear formula
isFromForm :: NoVars -> LinGraph -> Bool
isFromForm n lg = all (\(a,b,c,d) -> not (lg a b && not (lg a c) && not (lg a d) && lg b c && not (lg b d) && lg c d)) [(a, b, c, d) | a <- [0..(n-1)], b <- [0..(n-1)], c <- [0..(n-1)], d <- [0..(n-1)]]

-- |Generate a list of all graphs that arise from formulae We do this
-- by generating recursively the (valid) graphs of smaller dimension
-- and then enumerating the possible extensions of these graphs and
-- checking if these graphs are valid. The key point here is that
-- every subgraph of a valid graph is itself valid. Generating every
-- possible graph and then checking whether it is valid is
-- computationally infeasable.
allLinGraphsFromForm :: NoVars -> [ LinGraphC ]
allLinGraphsFromForm n
  | n == 0 = [ 0 ] -- There is precisely one empty graph
  | otherwise = do -- Introduces monadic notation, see comments below for the jist of what is happening
      x <- allLinGraphsFromForm (n - 1) -- For each graph with 'n-1' variables
      y <- [0 .. (2 ^ (n - 1) - 1)] -- And each combination of 'n-1' bits
      let z = y + (shiftL x $ n - 1) -- Shift the bits for the old variables and add the new ones via addition
      guard ((isFromForm n . fromCompressed n) z) -- Check if the generated graph is valid
      return z

-- |Determines the set of nodes which neighbour the input node. We
-- simply check them all. This is used in the algorithm below.
neighbourSet :: NoVars -> LinGraph -> Node -> S.Set Node
neighbourSet noVars lg n = S.fromList [ m | m <- [0 .. (noVars - 1)] , lg n m ]

-- |Type for storing the collection of max cliques in a graph.
type MCliques = [ S.Set Node ]

-- |Algorithm for finding all max cliques of a graph.
-- See https://en.wikipedia.org/wiki/Bron%E2%80%93Kerbosch_algorithm
bronKerbosch :: NoVars -> LinGraph -> S.Set Node -> S.Set Node -> S.Set Node -> MCliques
bronKerbosch noVars lg r p x
  | S.null p && S.null x = [ r ]
  | otherwise = go p x
    where
      go :: S.Set Int -> S.Set Int -> [ S.Set Int ]
      go p' x'
        | null p' = []
        | otherwise =
          let v = 0 `S.elemAt` p'
              nv = neighbourSet noVars lg v
          in bronKerbosch noVars lg (v `S.insert` r) (p' `S.intersection` nv) (x' `S.intersection` nv)
             ++ go (v `S.delete` p') (v `S.insert` x')

-- |Return all maximum cliques of a graph. This is done by starting
-- the above formula off with 'r = empty = x' and 'p' being the set of
-- all nodes.
maxCliques :: NoVars -> LinGraph -> MCliques
maxCliques noVars lg = bronKerbosch noVars lg S.empty (S.fromList [0 .. (noVars - 1)]) S.empty


-- |Returns a list of all valid graphs along with their max cliques.
allMaxCliques :: NoVars -> [ (LinGraphC, MCliques) ]
allMaxCliques noVars = map (\x -> (x, maxCliques noVars $ fromCompressed noVars x)) $ allLinGraphsFromForm noVars

-- |Given two lists of max cliques, determine if there is a linear
-- implication. Note we do not need the graphs to do this. We check
-- that for all 'p' in 'mc1' that there is any 'q' in 'mc2' such that
-- 'q' is a subset of 'p'
linearImplication :: MCliques -> MCliques -> Bool
linearImplication mc1 mc2 = all (\p -> any (`S.isSubsetOf` p) mc2) mc1

-- |Check if an implication is trivial at x. This is a similar
-- condition to above except we check that 'q' is a subset of 'p \
-- {x}'
isTrivialAt :: MCliques -> MCliques -> Node -> Bool
isTrivialAt mc1 mc2 x = all (\p -> any (`S.isSubsetOf` (S.delete x p)) mc2) mc1

-- |Check if an implication is trivial. An implication is trivial if
-- it is trivial at any node 'x'
isTrivial :: NoVars -> MCliques -> MCliques -> Bool
isTrivial noVars mc1 mc2 = any (isTrivialAt mc1 mc2) [0..(noVars-1)]

-- |Generates a list of all the valid graphs that are linearly implied by a given node
buildEdgesFrom :: MCliques -- ^The (max cliques of the) node to check.
               -> [ (LinGraphC, MCliques) ] -- ^The graphs to check for implications.
               -> [ (LinGraphC, MCliques) ] -- ^The output graphs that are implied by the node to check.
buildEdgesFrom c xs = filter (\(_,c2) -> c /= c2 && linearImplication c c2) xs

-- |Filter out all trivial edges from 'buildEdgesFrom'
buildNonTrivialEdgesFrom :: NoVars -> MCliques -> [ (LinGraphC, MCliques) ] -> [ (LinGraphC, MCliques) ]
buildNonTrivialEdgesFrom noVars c xs =
  let ys = buildEdgesFrom c xs
  in (filter (\(_,c2) -> not (isTrivial noVars c c2)) ys)

-- |Type for an inference graph. This is a map from 'Ints' (= Nodes) to sets of nodes.
type InfGraph = M.IntMap (S.Set LinGraphC)

-- |Build the inference graph of non trivial inferences.
buildGraph :: NoVars -- ^ Number of variables
           -> [ (LinGraphC, MCliques) ] -- ^ Input graphs with their cliques
           -> InfGraph -- ^ Output inference graph
buildGraph noVars xs = xs `deepseq` infgraph -- Make sure the inputs graphs are fully calculated before starting (Haskell is lazy)
  where
    infgraph = M.fromList parInfList
    -- ^ generate the map from a list
    edgesFrom x = buildNonTrivialEdgesFrom noVars (snd x) xs
    -- ^ calculate the edges from a specific vertex
    infList = map (\x -> (fst x, S.fromList (map fst $ edgesFrom x))) xs
    -- ^ put these in the right format for converting to a map
    parInfList = withStrategy (parListChunk 1000 rdeepseq) infList
    -- ^ Tell haskell to use parallisation to generate this list

-- | Given an inference graph and a node 'x', 'getMinimal' gets all
-- the minimal inferences from 'x'. That is nodes 'y' such that there
-- is no 'z' distinct from 'x' and 'y' with 'x -> z -> y'
getMinimal :: InfGraph -> LinGraphC -> S.Set LinGraphC
getMinimal ig x =
  let keys = (ig M.! x) -- All the things implied by 'x'
      transitiveImplied = S.unions ((ig M.!) <$> S.toList keys) -- All the things implied by the things implied by 'x'
  in keys S.\\ transitiveImplied -- 'y's implied by 'x' which are not implied by some 'z' with 'x -> z -> y'

-- |Determine whether an inference is given by the transitive closure of medial
isMedialStar :: NoVars -> LinGraph -> LinGraph -> Bool
isMedialStar noVars p q = cond1 && cond2
  where
    pairs = [(a,b) | a <- [0 .. (noVars - 1)], b <- [0 .. (noVars - 1)]]
    -- ^ all pairs of nodes
    cond1 = all (\(a,b) -> if p a b then q a b else True) pairs
    -- ^ The first condition is that the edges of 'p' must be a subset of edges of 'q'
    psquare a b c d = p a b && p c d && not (p a c) && not (p a d) && not (p b c) && not (p b d)
    qsquare a b c d = q a b && q c d && not (q a c) && q a d && q b c && not (q b d)
    cond2 = all (\(a,d) -> a == d || p a d || not (q a d) || any (\(b,c) -> psquare a b c d && qsquare a b c d) pairs) pairs
    -- ^ condition 2 says that for all pairs of nodes '(a,d)', with no
    -- edge a to d in 'p' and an edge a to d in 'q', there exists 'b'
    -- and 'c' such that in 'p' we have
    -- a -- b
    --
    -- c -- d
    -- which is checked by 'psquare'
    -- and in 'q' we have
    -- a -- b
    --   ><
    -- c -- d
    -- which is checked by 'qsquare'

-- | Get all partitions of a list into two sublists
partitions :: [a] -> [([a], [a])]
partitions [] = [([],[])]
partitions (x:xs) = do
  (a,b) <- partitions xs
  [(x:a,b), (a,x:b)]

-- | Given two sets of nodes, we determine if they are seperated by an
-- 'and' This happens when there is an edge between everything in the
-- first set and everything in the second set The idea is that if a
-- graph has nodes A = B 'disjointUnion' C, and 'B' and 'C' are
-- and-partitioned, then there is a linear formula 'a' of the form 'b
-- and c' where 'b' has variables 'B' and 'c' has variables 'C' and
-- 'A' represents 'a'
isAndPartition :: LinGraph -> [Node] -> [Node] -> Bool
isAndPartition lg a b = and [ lg x y | x <- a, y <- b ]

-- | Similar idea as above for 'or'. This time we check there is no
-- edge between anything in the first set and anything in the second
-- set
isOrPartition :: LinGraph -> [Node] -> [Node] -> Bool
isOrPartition lg a b = and [ not (lg x y) | x <- a, y <- b ]

-- | Check if two graphs are the same when restricted to a set of nodes
isInternallyUnchanged :: LinGraph -> LinGraph -> [Node] -> Bool
isInternallyUnchanged lg1 lg2 xs = and [ lg1 x y == lg2 x y | x <- xs, y <- xs ]

-- | Check if an inference is given by a single switch move
isSwitch :: NoVars -> LinGraph -> LinGraph -> Bool
isSwitch noVars lg1 lg2 = isSwitch' [0 .. (noVars-1)]
  where
    isSwitch' :: [Node] -> Bool
    -- ^ Checks if the inference is given by a switch involving the
    -- nodes in the given set
    isSwitch' xs = flip any (partitions xs) $ \(a,b) -> -- Search for a partition that satisfies:
      all (not . null) [a,b] -- Check the partition is not trivial
      && conditions a b -- Check further conditions
    conditions a b = cond1 a b || cond2 a b || cond3 a b
    -- ^ must satisfy one of the following three conditions:
    -- Condition one says that the inference is of the form A ∧ B -> A ∧ C where B -> C is a switch
    -- Condition two says that the inference is of the form A ∨ B -> A ∨ C where B -> C is a switch
    -- Condition three says there is a switch involving all the variables
    cond1 a b = isAndPartition lg1 a b -- Formula 1 can be represented 'A ∧ B'
      && isAndPartition lg2 a b -- Formula 2 can be represented 'A′ ∧ B′'
      && isInternallyUnchanged lg1 lg2 a -- 'A = A′'
      && isSwitch' b -- 'B -> B′' occurs as a single switch
    cond2 a b = isOrPartition lg1 a b && isOrPartition lg2 a b && isInternallyUnchanged lg1 lg2 a && isSwitch' b
    -- ^ Same as above but with an or at the top level
    cond3 a b = flip any (partitions b) $ \(c,d) -> -- Further split 'b' into 'c' 'd'
      all (not . null) [c, d] -- This partition was not trivial
      && all (isInternallyUnchanged lg1 lg2) [a, c, d] -- 'a,c,d' are not changed between the formulae
      && isAndPartition lg1 a b
      && isOrPartition lg1 c d -- Formula one has the form 'a ∧ (c ∨ d)'
      && isOrPartition lg2 (a ++ c) d
      && isAndPartition lg2 a c -- Formula two has the form '(a ∧ c) ∨ d'

-- Helper function for tallying up results
instance Semigroup Int where
  (<>) = (+)

instance Monoid Int where
  mempty = 0

-- | Classify each minimal non-trivial inference
classify :: NoVars -> LinGraph -> LinGraph -> (Int {- switches -},Int {- medials -},Int {- other -})
classify noVars lg1 lg2 =
  if isSwitch noVars lg1 lg2 then (1,0,0)
  else if isMedialStar noVars lg1 lg2 then (0,1,0)
  else (0,0,1)

-- | Helper function to save an inference graph to a file so that we
-- don't need to recompute it every time.
retrieveGraph :: FilePath -> InfGraph -> IO InfGraph
retrieveGraph filename graph = do
  b <- doesFileExist filename
  if b then putStrLn ("Found file " ++ filename) >> deserialise <$> BS.readFile filename
    else do
    putStrLn $ "Could not find " ++ filename ++ " so will build"
    (BS.writeFile filename . serialise) graph
    return graph

-- | Main program
main :: IO ()
main = go 7
  where
    go :: NoVars -> IO ()
    -- ^ Call main method specifying the number of variables
    go noVars = do
      g <- retrieveGraph ("graphs/InfGraph_" ++ show noVars) (buildGraph noVars (allMaxCliques noVars))
      -- Build the inference graph (or retrive a saved one)
      print (M.size g)
      -- Print its size
      let g2 = M.mapWithKey (\k _ -> getMinimal g k) g
      -- Get an inference graph of minimal inferences
      retrieveGraph ("graphs/MinInfGraph_" ++ show noVars) g2
      -- Retrieve the saved minimal inference graph (or build it)
      let infs = M.foldrWithKey (\k a b -> (map (\x -> (k,x)) $ S.toList a) ++ b) [] g2
      -- Get a list of all the inferences
      let classifiedInfs = map (\(x,y) -> classify noVars (fromCompressed noVars x) (fromCompressed noVars y)) infs
      -- Classify all inferences
      let parClassInfs = withStrategy (parListChunk 1000 rdeepseq) $ classifiedInfs
      -- Calculate this in parallel
      let tally = mconcat parClassInfs
      -- Tally the results
      print tally
      -- and print

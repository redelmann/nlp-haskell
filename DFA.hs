{-# LANGUAGE BangPatterns #-}

-- Copyright 2014 Romain Edelmann. All Rights Reserved.

{- | This module defines DFAs and the edit distance.

     This was developed as part of a pratical session on Spelling Error
     Correction in the Introduction to Natural Language Processing
     course at EPFL. -}
module DFA where

import Prelude hiding (lookup)
import Control.Arrow (first, second)
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.Writer
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromJust, isJust)
import Data.Vector (Vector, (!?))
import qualified Data.Vector as Vector
import Data.Vector.Mutable (STVector)
import qualified Data.Vector.Mutable as MVector

-- * DFA

-- ** Definition

-- | Deterministic Finite State Automaton, with final states
--   holding a value of type `a` and transitions labeled by values
--   of type `c`.
data DFA c a = DFA
    { initial :: Int
    , states  :: Vector (Maybe a, Map c Int) }
    deriving Show

instance Functor (DFA c) where
    fmap f (DFA i ss) = DFA i $ fmap (first $ fmap f) ss

-- ** Building

-- | Builds a DFA from a list of states.
--   Each state is described by its value if it is final,
--   and the list of its transitions.
build :: Ord c
      => Int  -- ^ The initial state index.
      -> [(Maybe a, [(c, Int)])]  -- ^ The list of states.
      -> DFA c a
build i = DFA i . Vector.fromList . map (second Map.fromList)

-- | Internal state used by the `fromList` function.
data BuildState s a c = BuildState
    { nextState :: !Int
    , vector    :: !(STVector s (Maybe a, Map c Int)) }

-- | Builds a DFA from a list of possible paths with their values.
fromList :: Ord c => [([c], a)] -> DFA c a
fromList xs = runST $ do
    -- Creating new vector
    v <- MVector.new 1
    -- Inserting the initial state
    MVector.write v 0 (Nothing, Map.empty)
    -- Insert all words
    (BuildState s v') <- foldM go (BuildState 1 v) xs
    -- Freeze the vector and return the DFA representation
    fmap (DFA 0 . Vector.take s) $ Vector.freeze v'
  where
    go bs (xs, a) = lookupInsert bs 0 xs a

    -- Looks up a transition or inserts it.
    lookupInsert (BuildState n v) i [] a = do
        -- Read the node i
        (_, ts) <- MVector.read v i
        -- Set the value at this node
        MVector.write v i (Just a, ts)
        -- Return the original build state
        return (BuildState n v)
    lookupInsert (BuildState n v) i (x : xs) a = do
        -- Read the node i
        (ma, ts) <- MVector.read v i
        case Map.lookup x ts of
            -- In case the transition is already there, follow it
            Just k -> lookupInsert (BuildState n v) k xs a
            -- If it is not, create a new node and add the transition
            Nothing -> do
                v' <- createNode n v
                MVector.write v' i (ma, Map.insert x n ts)
                -- Follow the newly inserted transition
                lookupInsert (BuildState (n + 1) v') n xs a

    -- Creates a new node.
    createNode n v = do
        -- Grow the vector by factor 2 in case it is not big enough
        v' <- if MVector.length v <= n then MVector.grow v n else return v
        -- Insert an empty node at the given position
        MVector.write v' n (Nothing, Map.empty)
        -- Return the possibly new vector
        return v'

-- ** Querying

-- | Looks up a value in the DFA.
lookup :: Ord c
       => [c]  -- ^ The list of transitions to take.
       -> DFA c a  -- The automaton.
       -> Maybe a
lookup [] (DFA q ss) = join $ fmap fst $ ss !? q
lookup (x : xs) (DFA q ss) = do
    ts <- fmap snd $ ss !? q
    n  <- Map.lookup x ts
    lookup xs (DFA n ss)

-- | Returns the list of all paths ending in a final state
--   that are within a certain distance of a given path.
--
-- For each match, return the path, the value at the corresponding final state and
-- the distance from the reference path.
atDistance :: (Eq c)
           => Int  -- ^ The distance.
           -> [c]  -- ^ The reference path.
           -> DFA c a  -- ^ The automaton.
           -> [([c], a, Int)]
atDistance d xs (DFA q ss) = runST $ do
    -- Create a vector for the dynamic program
    v <- MVector.new s
    -- Executes the monadic action.
    flip evalStateT v $ execWriterT $ handleNode 0 q []
  where
    -- Utility functions
    liftST a = lift $ lift a
    index i j = j + i * s
    -- Reference path as a vector
    w = Vector.fromList xs
    -- Number of prefixes of the reference paths
    s = Vector.length w + 1

    -- | Executes at a given node.
    --
    -- - i  is the length of the prefix
    -- - a  is the current state index
    -- - ys is the prefix is reverse order
    handleNode i a ys = case ss !? a of
        Nothing -> return ()  -- No such state, we do nothing
        Just (mv, ts) -> do
            -- Fix the size of the vector, if necessary
            ensureColumnExists i
            -- Compute the column i
            computeColumn i
            -- Lookup the cut off distance
            dc <- distanceCutOff i
            -- Check if we are within the cut off distance
            when (dc <= d) $ do
                -- Handle the case when its a final state
                when (isJust mv) $ do
                    -- Lookup the distance
                    dw <- distanceWithWord i
                    -- When the distance is small enough, add an answer
                    when (dw <= d) $ tell [(reverse ys, fromJust mv, dw)]
                -- Recurse over all the transitions
                forM_ (Map.assocs ts) $ \ (y, b) ->
                    handleNode (i + 1) b (y : ys)
      where
        -- | Returns the letter at a given position in the given word
        letterAt 0 = Nothing
        letterAt n = w !? (n - 1)

        -- | Returns the letter at the given position
        --   from the end of the current prefix
        letterFromPrefixEnd i = case drop i ys of
            (x : _) -> Just x
            _       -> Nothing

        -- | Ensures that the vector is big enough to fit column i.
        ensureColumnExists i = do
            v <- get
            when (MVector.length v < (i + 1) * s) $ do
                !v' <- liftST $ MVector.grow v (MVector.length v)
                put v'
                ensureColumnExists i

        -- | Recomputes the column.
        computeColumn 0 = do
            -- Handles the leftmost column
            v <- get
            forM_ [0 .. s - 1] $ \ i -> liftST $ MVector.write v i i
        computeColumn k = do
            v <- get
            -- Writes the first row for the column
            liftST $ MVector.write v (index k 0) k
            -- Computes for each row the minimal cost
            forM_ [1 .. s - 1] $ \ j -> do
                -- Gets the list of possible costs
                costs <- costOfEqual k j `withPriorityOverAll`
                    [ costOfInsertion k j
                    , costOfDeletion k j
                    , costOfTranspose k j `withPriorityOver` costOfSubstitution k j ]
                -- Write the minimum cost at the given index
                liftST $ MVector.write v (index k j) $ minimum costs
          where
            -- | Prefer `a` if it provides a value, otherwise resort to all of the `bs`.
            a `withPriorityOverAll` bs = do
                mv <- a
                case mv of
                    Nothing -> fmap catMaybes $ sequence bs
                    Just va -> return [va]

            -- | Prefer `a` if it provides a value, otherwise resort to `b`.
            a `withPriorityOver` b = do
                mv <- a
                case mv of
                    Just _ -> return mv
                    Nothing -> b

            -- Cost for equality.
            costOfEqual i j = if letterFromPrefixEnd 0 /= letterAt j
                then return Nothing
                else fmap Just $ costAt (i - 1) (j - 1)

            -- | Cost for insertion.
            costOfInsertion i j = fmap (Just . (+ 1)) $ costAt (i - 1) j

            -- | Cost for deletion.
            costOfDeletion i j = fmap (Just . (+ 1)) $ costAt i (j - 1)

            -- | Cost of transpostion.
            costOfTranspose i j
                | j < 2 || i < 2 = return Nothing
                | letterAt (j - 1) == letterFromPrefixEnd 0 &&
                  letterAt j == letterFromPrefixEnd 1 = fmap (Just . (+ 1)) $ costAt (i - 2) (j - 2)
                | otherwise = return Nothing

            -- Cost of substitution.
            costOfSubstitution i j = fmap (Just . (+ 1)) $ costAt (i - 1) (j - 1)

        -- | Computes the cut off distance given that the vector has been properly set.
        distanceCutOff i = fmap (minimum . ((d + 1) :)) $ mapM (costAt i) $
            takeWhile (< s) $ dropWhile (< 0) [i - d .. i + d]

        -- | Computes the distance with the reference word,
        --   given that the vector has been properly set.
        distanceWithWord i = do
            v <- get
            costAt i (s - 1)

        -- | Gets the cost at a given position.
        costAt i j = do
            v <- get
            liftST $ MVector.read v $ index i j


-- * Examples

-- | Language given as example.
abLanguage :: DFA Char ()
abLanguage = build 0
    [ (Just (), [('a', 1), ('b', 3)])
    , (Nothing, [('b', 2)])
    , (Nothing, [('a', 0)])
    , (Nothing, [('a', 4)])
    , (Nothing, [('b', 0)]) ]

-- | An other example, built using `fromList`.
otherExample :: DFA Char Int
otherExample = fromList [("hello", 1), ("world", 2), ("hell", 2), ("help", 3), ("helping", 7)]

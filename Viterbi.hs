-- Copyright 2014 Romain Edelmann. All rights reserved.

{- | This module defines Hidden Markov Models and the Viterbi algorithm.

     This was developed as part of a pratical session on Part-of-Speech tagging
     in the Introduction to Natural Language Processing course at EPFL. -}
module Viterbi where

import           Control.Monad.State hiding (forM_)
import           Data.Foldable       (Foldable, foldl', forM_)
import           Data.Map            ((!))
import qualified Data.Map            as Map
import           Data.Ord            (comparing)

-- * Hidden Markov Models

-- ** Model definition

{- | Definition of a Hidden Markov Model.

     `f` should be a foldable functor used to contain the universe of states,
     `s` is the type of the states, `o` the type of the oberservations and
     `p` the numeric type for the probabilities.

     For arbitrary precision, `p` should be `Rational`. -}
data Model f s o p = Model
    { stateUniverse         :: f s  -- ^ Possible states, should be finite.
    , transitionProbability :: s -> s -> p  -- ^ Probability of transitions.
    , emissionProbability   :: s -> o -> p  -- ^ Probability of emissions.
    , initialProbability    :: s -> p -- ^ Starting probability of states.
    }

-- ** Viterbi algorithm

{- | Returns a list of hidden states sequences that maximize the likelyhood
     of producing the given observations in the given model. -}
viterbiFrom :: (Foldable f, Functor f, Ord p, Num p, Ord s)
            => Model f s o p  -- ^ Parameters of the model.
            -> [o]  -- ^ Sequence of observations.
            -> [[s]]  -- ^ Most probable states sequences.
viterbiFrom ps = viterbi (stateUniverse ps) (transitionProbability ps)
                         (emissionProbability ps) (initialProbability ps)

{- | Returns a list of hidden states sequences that maximize the likelyhood
     of producing the given observations in the given model. -}
viterbi :: (Foldable f, Functor f, Ord p, Num p, Ord s)
        => f s  -- ^ Universe of states
        -> (s -> s -> p)  -- ^ State transition probabilities.
        -> (s -> o -> p)  -- ^ Emission probabilities.
        -> (s -> p)  -- ^ Initial state probabilities.
        -> [o]  -- ^ Sequence of observations.
        -> [[s]]  -- ^ Most probable state sequences.
viterbi _      _      _     _       []       = []
viterbi states goesTo emits startAt (x : xs) = flip evalState Map.empty $ do
    -- Initialisation, setting the value for the first observation
    forM_ states $ \ s ->
        modify $ Map.insert s (startAt s * s `emits` x, [[s]])
    -- Executing the following observations
    forM_ xs $ \ x' -> do
        prev <- get  -- Fetch the values from the previous step
        forM_ states $ \ s -> do
            {- Find the most likely paths leading to the current state,
               with the associated probability -}
            let (ts, prob : _) = unzip $ maximumsBy (comparing snd) $
                                 fmap stepFrom states
                stepFrom t = (t, fst (prev ! t) * t `goesTo` s * s `emits` x')
                paths = concat [ map (s :) $ snd $ prev ! t | t <- ts ]
            -- Set the new values associated to the current state
            modify $ Map.insert s (prob, paths)
    -- Take the most probable final state and return the path leading to it
    fmap (concatMap (map reverse . snd) . maximumsBy (comparing fst)) get
  where
    -- Returns the list of all maximal elements
    maximumsBy f = foldl' go []
      where
        go [] y = [y]
        go zs y = case f y (head zs) of
            LT -> zs  -- The current element is smaller than the maxs
            EQ -> y : zs  -- The current element is also a max
            GT -> [y]  -- The current element is larger than the previous maxs


-- * Path probability

{- | Returns the probability that a given sequence of state transitions
     and emissions where produced by a given model. -}
probabilityFrom :: (Num p)
                => Model f s o p  -- ^ Parameters of the model.
                -> [o]  -- ^ List of observations.
                -> [s]  -- ^ List of states.
                -> p  {- ^ Probability that model took the given
                           transitions and emitted the given values. -}
probabilityFrom ps = probability (transitionProbability ps)
                                 (emissionProbability ps)
                                 (initialProbability ps)

{- | Returns the probability that a given sequence of state transitions
     and emissions where produced by a given model. -}
probability :: (Num p)
            => (s -> s -> p)  -- ^ State transition probabilities.
            -> (s -> o -> p)  -- ^ Emission probabilities.
            -> (s -> p)  -- ^ Initial state probabilities.
            -> [o]  -- ^ Sequence of observations.
            -> [s]  -- ^ Sequence of states.
            -> p  -- ^ Probability of the given sequence of states.
probability transfersTo emits initiallyAt observations states
    | not $ sameLength observations states = 0
    | null states = 1
    | otherwise = -- Probability of starting at the given state
                  initiallyAt (head states) *
                  -- Probability of emitting the observed values
                  product (zipWith emits states observations) *
                  -- Probability of making the given transitions
                  product (zipWith transfersTo states (tail states))
  where
    sameLength (_ : as) (_ : bs) = sameLength as bs
    sameLength [] [] = True
    sameLength _ _ = False

-- * Examples

-- ** Example from the lecture

-- | Model from the course slides.
modelSlides :: Model [] Char Char Rational
modelSlides = Model
    { stateUniverse = "12"
    , transitionProbability = curry (transitions !)
    , emissionProbability = curry (emissions !)
    , initialProbability = (starts !) }
  where
    transitions = Map.fromList
        [ (('1', '1'), 0.4)
        , (('1', '2'), 0.6)
        , (('2', '1'), 0.9)
        , (('2', '2'), 0.1) ]

    emissions = Map.fromList
        [ (('1', 'H'), 0.49)
        , (('1', 'T'), 0.51)
        , (('2', 'H'), 0.85)
        , (('2', 'T'), 0.15) ]

    starts = Map.fromList
        [ ('1', 0.5)
        , ('2', 0.5) ]

{- | Running on the example observations from the slides. -}
exSlides :: [String]
exSlides = viterbiFrom modelSlides "HTTHTTHHTTHTTTHHTHHTTHTTTTHTHHTHTHHTTTH"

-- ** Example from Wikipedia

-- | Model from Wikipedia article on the Viterbi algorithm.
modelWiki :: Model [] String String Rational
modelWiki = Model
    { stateUniverse = ["Healthy", "Sick"]
    , transitionProbability = transfersTo
    , emissionProbability = emits
    , initialProbability = startingAt }
  where
    "Healthy" `transfersTo` "Healthy" = 0.7
    "Healthy" `transfersTo` "Sick"    = 0.3
    "Sick"    `transfersTo` "Sick"    = 0.6
    "Sick"    `transfersTo` "Healthy" = 0.4
    _         `transfersTo` _         = 0.0

    "Healthy" `emits` "Normal" = 0.5
    "Healthy" `emits` "Dizzy"  = 0.1
    "Healthy" `emits` "Cold"   = 0.4
    "Sick"    `emits` "Normal" = 0.1
    "Sick"    `emits` "Dizzy"  = 0.6
    "Sick"    `emits` "Cold"   = 0.3
    _         `emits` _        = 0.0

    startingAt "Healthy" = 0.6
    startingAt "Sick"    = 0.4
    startingAt _         = 0.0

{- | Example from Wikipedia article on the Viterbi algorithm.

   > > exWiki
   > [["Healthy","Healthy","Sick"]] -}
exWiki :: [[String]]
exWiki = viterbiFrom modelWiki ["Normal", "Cold", "Dizzy"]

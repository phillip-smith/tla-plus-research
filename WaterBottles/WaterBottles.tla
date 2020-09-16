---------------------------- MODULE WaterBottles ----------------------------
(***************************************************************************)
(* The Water Bottles problem is a fairly trivial reasoning problem. In     *)
(* this problem, one is provided two bottles: one with a 3 liter capacity, *)
(* and one with a 5 liter capacity. A hose is available to fill either     *)
(* bottle, and the contents of a bottle can be poured on the ground to     *)
(* empty it. Bottles have no graduation marks, and cannot be marked or     *)
(* otherwise drawn on. The only possible actions are completely filling    *)
(* either bottle, emptying a bottle, or transferring as much of the        *)
(* contents of one bottle as can fit into the other.                       *)
(*                                                                         *)
(* Based on these constraints, the goal of the problem is to fill the 5    *)
(* liter bottle with exactly 4 liters of water.                            *)
(*                                                                         *)
(* This TLA+ specification describes the states involved in this system,   *)
(* as the possible operations to the system. We define an invariant        *)
(* relating to levels in the water bottles, and then an invariant which we *)
(* will disprove in order to come to the solution.                         *)
(*                                                                         *)
(* The output of TLC is included at the end of this document for           *)
(* completeness. The source document included in this repository includes  *)
(* the source used to produce this document, in TLA+ format, which can be  *)
(* passed to TLC in order to prove the assertions made herein.             *)
(*                                                                         *)
(* It should also be noted that this is part of a learning project;        *)
(* proving the water bottle problem to be solvable is not novel in any     *)
(* way, but serves as a simple demonstration of TLA+ and its toolchain.    *)
(***************************************************************************)

(***************************************************************************)
(* This statement pulls in basic arithmetic operations, as well as ranges. *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* This system has only two state variables.                               *)
(***************************************************************************)
VARIABLES
    small, \* the amount of water in the small bottle
    large  \* the amount of water in the large bottle

(***************************************************************************)
(* Invariant which states that the small bottle can have between 0 and 3   *)
(* liters of water, and the large bottle can have between 0 and 5 liters   *)
(* of water.                                                               *)
(***************************************************************************)
TypeOK == 
    /\ small \in 0..3
    /\ large \in 0..5

(***************************************************************************)
(* The invariant which we will disprove using TLC. By defining it this     *)
(* way, we can run TLC and find sequence which violates this invariant;    *)
(* this sequence is necessarily the solution to the water bottle problem.  *)
(***************************************************************************)
NoFoundSolution ==
    /\ large /= 4

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next, we define each state transition. At any point, a 'step' in our    *)
(* system is defined as fulfilling one of these conditions. The            *)
(* implementation of that 'step' logic will be defined after the steps     *)
(* themselves.                                                             *)
(***************************************************************************)

(***************************************************************************)
(* Fill the small bottle to its capacity of 3 liters                       *)
(***************************************************************************)
FillSmall ==
    /\ small' = 3
    /\ UNCHANGED << large >>

(***************************************************************************)
(* Fill the large bottle to its capacity of 5 liters                       *)
(***************************************************************************)
FillLarge ==
    /\ large' = 5
    /\ UNCHANGED << small >>

(***************************************************************************)
(* Empty the contents of the small bottle                                  *)
(***************************************************************************)
EmptySmall ==
    /\ small' = 0
    /\ UNCHANGED << large >>

(***************************************************************************)
(* Empty the contents of the large bottle                                  *)
(***************************************************************************)
EmptyLarge ==
    /\ large' = 0
    /\ UNCHANGED << small >>

(***************************************************************************)
(* Pour the contents of the large bottle into the small bottle             *)
(***************************************************************************)
LargeToSmall ==
    IF small + large > 3
        \* Handle the case where the large bottle's contents would overflow the small bottle
        THEN /\ small' = 3
             /\ large' = large - (3 - small)
        \* Otherwise, pour the entire contents of the large bottle into the small bottle
        ELSE /\ small' = small + large
             /\ large' = 0

(***************************************************************************)
(* Pour the contents of the small bottle into the large bottle             *)
(***************************************************************************)
SmallToLarge ==
    IF small + large > 5
        \* Handle the case where the small bottle's contents would overflow the large bottle
        THEN /\ small' = small - (5 - large)
             /\ large' = 5
        \* Otherwise, pour the entire contents of the small bottle into the large bottle
        ELSE /\ small' = 0
             /\ large' = small + large

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next, we define the initial state for the system as having both bottles *)
(* empty, represented as having 0 liters of water.                         *)
(***************************************************************************)
Init ==
    /\ small = 0
    /\ large = 0

(***************************************************************************)
(* This defines the function for a 'step' in the system, capturing all     *)
(* valid state transitions as the disjunction of the steps listed above.   *)
(***************************************************************************)
Next ==
    \/ FillSmall
    \/ FillLarge
    \/ EmptySmall
    \/ EmptyLarge
    \/ LargeToSmall
    \/ SmallToLarge

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following is the abbreviated output of running TLC against the      *)
(* above definitions. Line numbers and references have been removed for    *)
(* brevity.                                                                *)
(* *)
(* Intuitively, the steps below are a solution to the water bottle         *)
(* problem. Note that this isn't exhaustive; there are other ways to       *)
(* arrive at a solution, but that isn't what we're solving for here. The   *)
(* sole purpose of this is to formally prove the solvability of the        *)
(* problem.                                                                *)
(***************************************************************************)

(***************************************************************************)
(* Error: Invariant NoFoundSolution is violated.                           *)
(* Error: The behavior up to this point is:                                *)
(*                                                                         *)
(* State 1: <Initial predicate>                                            *)
(* /\ large = 0                                                            *)
(* /\ small = 0                                                            *)
(*                                                                         *)
(* State 2: <FillLarge>                                                    *)
(* /\ large = 5                                                            *)
(* /\ small = 0                                                            *)
(*                                                                         *)
(* State 3: <LargeToSmall>                                                 *)
(* /\ large = 2                                                            *)
(* /\ small = 3                                                            *)
(*                                                                         *)
(* State 4: <EmptySmall>                                                   *)
(* /\ large = 2                                                            *)
(* /\ small = 0                                                            *)
(*                                                                         *)
(* State 5: <LargeToSmall>                                                 *)
(* /\ large = 0                                                            *)
(* /\ small = 2                                                            *)
(*                                                                         *)
(* State 6: <FillLarge>                                                    *)
(* /\ large = 5                                                            *)
(* /\ small = 2                                                            *)
(*                                                                         *)
(* State 7: <LargeToSmall>                                                 *)
(* /\ large = 4                                                            *)
(* /\ small = 3                                                            *)
(***************************************************************************)
=============================================================================
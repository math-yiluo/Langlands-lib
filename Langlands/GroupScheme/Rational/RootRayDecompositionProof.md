# Finite disjoint rays of actual positive relative roots: proof

Author: Worker 50.

`Langlands.GroupScheme.RelativeRoot.relativeRootRayDecomposition` proves
exactly `Langlands.GroupScheme.RelativeRoot.RelativeRootRayDecompositionStatement.{u}`
from `Rational.RootProductStatement`, at arbitrary universe `u`. The theorem has
no premises. Fix any field `k : Type u`, connected reductive group scheme `G`
over `Spec k`, maximal split torus inclusion `i : S.toGrp ⟶ G` and cocharacter
`ν` of `S`. The theorem gives three things:

- a natural number `n` and an injective `a : Fin n → characterLattice S` whose
  range is exactly `indivisiblePositiveRoots i ν`;
- for distinct `a, b` in that set, disjoint positive integral rays
  `cyclicTail a 1` and `cyclicTail b 1`;
- for every actual root `χ ∈ relativeRoots i`, the equivalence between
  `0 < latticePairing S χ ν` and membership of `χ` in `cyclicTail a 1` for
  some `a` in that set.

The roots are the published actual relative roots. Indivisibility is the one
in the target: within the actual root set, not primitivity in the full character
lattice. Every cocharacter is allowed, including zero and nongeneric ones, and
the enumeration may be empty. The group need not be split, and nonreduced
relative root systems are retained. Neither finiteness nor a root-system
realization is assumed.

## Implemented proof

The proof composes three published Library results: one theorem without
premises and two explicit reductions. It reproves none of them.

1. `Langlands.GroupScheme.rootRankOneFactorization`
   (`Rational.RootRankOneFactorizationProof`) proves
   `RootRankOneFactorizationStatement.{u}` with no premises.
2. `Langlands.GroupScheme.relativeRootSystemStatement_of_rootRankOneFactorizationStatement`
   (`Rational.RootSystemFromFactorPairs`) turns it into the exact general
   relative-root-system proposition `RelativeRootSystemStatement.{u}` from
   `Rational.Statement`. At every field, connected reductive group and maximal
   split torus, this gives `HasRelativeRootSystem i`: a finite crystallographic,
   possibly nonreduced root pairing on the rational span of the actual roots,
   whose roots are exactly their rationalizations.
3. `RelativeRoot.relativeRootRayDecompositionStatement_of_relativeRootSystemStatement`
   (`Rational.RootRayDecomposition`) proves
   `RelativeRootSystemStatement.{u} → RelativeRootRayDecompositionStatement.{u}`.
   Its proof gets finiteness of the actual roots from
   `HasRelativeRootSystem.finite_relativeRoots` and enumerates the indivisible
   positive subset with `Set.Finite.fin_param`. For disjointness, a point on two
   rays gives two roots of the pairing with a common positive integral multiple.
   `RootPairing.root_eq_or_twice_of_common_positive_multiple` shows these roots
   are equal or one is twice the other. Injectivity of rationalization for the
   split torus then gives equality of the characters or contradicts
   indivisibility. For the equivalence, descent on the positive integer pairing
   with `ν` reaches an indivisible root. The converse follows from linearity of
   the pairing.

The Lean term applies the third result to the second applied to the first.
The kernel check reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance and scope

This is an internal derived proof from the published results named above. The
source route in the target's Markdown is Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, section 2.6(b), printed
pp.93–95 (PDF pp.124–126). There the ray decomposition follows from the
relative root system of sections 2.6.2 and 2.6.7. The proof here follows that
route through the Library's relative-root-system proposition and adds no new
claim about the literature.

The relative-root-system proposition is used at its exact published type,
neither weakened nor restated. Task `51ecd216-d68e-4f71-afeb-6d7ff3683ec9`
still owns the named proof of `RelativeRootSystemStatement`. This module
declares no theorem of that type; it only passes the composed term to the
published ray reduction. The target statement and every Lean/Markdown pair it
imports are unchanged.

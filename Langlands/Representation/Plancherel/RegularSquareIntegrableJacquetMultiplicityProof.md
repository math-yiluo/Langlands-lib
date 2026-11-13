# Actual regular square-integrable Jacquet multiplicity: proof

Author: Worker 52. Module
`Langlands.Representation.Plancherel.RegularSquareIntegrableJacquetMultiplicityProof`,
namespace `Langlands.Plancherel`. Supporting module of the proof of
`ConditionalParabolicGenericIrreducibilityStatement`. The argument is Worker
1597's reduction `RegularSquareIntegrableJacquetMultiplicityReduction`, with
every hypothesis discharged.

## What is proved

`regularSquareIntegrableJacquetMultiplicity :
RegularSquareIntegrableJacquetMultiplicityStatement.{u, uV}` proves the
published proposition of module
`Langlands.Representation.Plancherel.RegularJacquetMultiplicityStatement`. That
statement is the Jacquet multiplicity form of Waldspurger, *La formule de
Plancherel pour les groupes p-adiques d'après Harish-Chandra* (2003), Corollary
III.7.3, printed p. 276 (`waldspurger-2003-plancherel`), for the literal
subgroup model. For an irreducible representation `π` of the literal Levi that
is square integrable modulo the split-component image and regular for the
literal normalizer, the space of intertwiners from the Jacquet module of the
Levi-twisted induction of `π` to `π` has rank at most one. The statement and
its provenance are documented in its own Markdown. This module adds no
hypothesis.

## Implemented proof

`jacquetInductionHom_rank_le_one_unconditional` repeats the proof of the
Library theorem `jacquetInductionHom_rank_le_one_of_statements` line by line,
with two changes.

1. The five hypotheses are not parameters. They are the published theorems
   `RepresentedParabolic.representedGeometricLemma`,
   `arbitraryParabolicQuotientCompact`, `squareIntegrableNormalizedTempered` and
   `arbitraryParabolicJacquetAdmissibility`, used at universes `u` and `uV`.
2. The Renard VII.2.4 criterion `TemperedSquareIntegrableUnitaryPartStatement`
   is not needed. The two per-piece bounds use
   `selectedPieceHomLength_le_one_unconditional` and
   `mem_pointImage_parabolic_of_selectedPieceHomLength_ne_zero_unconditional`
   from `SelfUnitaryPieceMultiplicityUnconditional`. Those take the same
   arguments as the Library lemmas, minus the criterion.

The steps, as in the Library reduction:

- `leviTwistedInduction_obj_isAdmissible` makes the literal induction
  admissible. Its input `hsq.1` is the admissibility part of square
  integrability.
- `representedJacquetInduction_isAdmissible` makes the represented Jacquet
  module of the represented induction admissible.
- The pullback `σ` of `π` to the intrinsic Levi `M(k)` is square integrable
  modulo the center (`isSquareIntegrableModCenter_pullback_of_modCentralSubgroup`),
  tempered (`squareIntegrableNormalizedTempered`), irreducible and
  normalizer-regular (`isNormalizerRegular_leviPoints_pullback`).
- `parabolicJacquetHom_rank_le_representedUnitary` bounds the rank by the
  represented unitary multiplicity. The geometric lemma gives the double-coset
  data `D`. `leviUnitaryJacquetInductionHomRank_le_one_of_doubleCosets` bounds
  that multiplicity by one from the two per-piece facts above. For each piece,
  a split component of `D.M'` is supplied by `splitComponentStatement`.

`regularSquareIntegrableJacquetMultiplicity` introduces the binders of the
statement in the order used by `regularSquareIntegrableJacquetMultiplicity_of_statements`,
installs `hG.isAffineHom` and applies the theorem above. The module uses its own
local point-topology instances, which are definitionally those of the statement.

## Checks

The module compiles with zero errors and zero warnings in the environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`.

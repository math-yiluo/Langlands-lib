# The cuspidal pair pole theorem from its functional-equation, local and real growth inputs

This module expresses `Langlands.Global.CuspidalPairPoleStatement` (Getz–Hahn, Theorem 11.7.1;
Cogdell 2004, Theorems 4.1–4.2) as a consequence of named propositions, in the two original
universes `u` (number field) and `uQ` (factor universe of the spectral presentations).

## Statements

`CuspidalPairPoles.CuspidalPairPoleRemainingInputsStatement.{u,uQ}` is the implication from the
following eight propositions to `CuspidalPairPoleStatement.{u,uQ}`:

- `CuspidalPairGlobalFunctionalEquationStatement.{u,uQ}`, the completed global Rankin–Selberg
  functional equation of cuspidal pairs;
- `RankinSelbergGlobal.RealOrdinaryNormalizedContinuationStatement`,
  `RankinSelbergGlobal.RealOrdinaryNormalizedGenerationStatement` and
  `RankinSelbergGlobal.ComplexOrdinaryNormalizedGenerationStatement`, the real continuation and
  the real and complex generation conclusions of Jacquet's archimedean theory for the ordinary
  tests (module `ArchimedeanOrdinaryNormalizedTests`);
- `RealOrdinaryNormalizedStripGrowthStatement`, exponential strip growth of the real ordinary
  normalizations (module `CuspidalPairPoleFromLocalTests`);
- `RankinSelbergGlobal.InfiniteWhittakerSliceModelStatement.{u,uQ}`,
  `RealPlaceWhittakerRestrictionSurjectivityStatement.{u}` and
  `ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u}`, the archimedean Whittaker
  slice model and the surjectivity of the actual restrictions onto the real and complex
  coefficient models (module `CuspidalPairPoleLocalRanges`).

`CuspidalPairPoles.CuspidalPairPoleRealPremisesStatement.{u,uQ}` is the same implication with
the strip growth premise replaced by the premises of
`RankinSelbergGlobal.RealOrdinaryStripGrowthPremisesStatement` (module
`RealOrdinaryStripGrowthReduction`): `RealWhittakerModelUniformityStatement`,
`RealUniformPrincipalSeriesInclusionStatement`, the canonical range, canonical evaluation and
matrix-coefficient premises of the real equal-rank successor step, and unequal real
character-list growth `RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h` for all
`t < r`.

## Proofs

`cuspidalPairPoleRemainingInputs` applies the Library's reduction
`cuspidalPairPoleFromLocalTests`. Its local input `CuspidalPairOrdinaryLocalInputs` is assembled
as follows:

- `ArchimedeanOrdinaryNormalizedTestsStatement` from the real continuation, the complex
  continuation (first component of the Library's `complexOrdinaryNormalizedAllGrowth`) and the
  real and complex generation premises;
- the real strip growth premise;
- the complex strip growth `ComplexOrdinaryNormalizedStripGrowthStatement`, the second
  component of `complexOrdinaryNormalizedAllGrowth`;
- `SpecifiedWhittakerSliceComparisonAt` over every number field, from the three Whittaker range
  premises by the Library's `specifiedWhittakerSliceComparisonAt_of_local`.

`cuspidalPairPoleRealPremises` obtains the real strip growth from its premises by
`realOrdinaryStripGrowthPremises` and applies `cuspidalPairPoleRemainingInputs`.

Neither theorem proves any of its premises.

## Provenance

This is an internal assembly along the route of the Library's `cuspidalPairPoleFromLocalTests`:
the ordinary global Rankin–Selberg integrals of J. W. Cogdell, *Analytic theory of L-functions
for GL_n* (2004), §4, Theorems 4.1–4.2, printed pp. 219–222, with the archimedean local theory
of H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorems 2.1, 2.3, 2.6 and 2.7,
author-posted pp. 6–10. The target is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Theorem 11.7.1, printed p. 309.

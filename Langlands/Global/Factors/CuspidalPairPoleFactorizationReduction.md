# The cuspidal pair functional equation and pole theorem from the archimedean factorization

This module derives the completed global Rankin–Selberg functional equation of actual
cuspidal pairs, `CuspidalPairGlobalFunctionalEquationStatement.{u, uQ}`, from a single
premise: the archimedean factorization
`RankinSelbergGlobal.ArchimedeanFactorizationStatement.{u, uQ}`. Everything else the
derivation uses is a proved Library theorem. It then derives the cuspidal pair pole
proposition `CuspidalPairPoleStatement.{u, uQ}` from the archimedean factorization and the
two real-place statements `RealOrdinaryNormalizedContinuationStatement` and
`RealOrdinaryNormalizedGenerationStatement`.

The module proves none of these three premises. It proves the real-place functional equation
without premises and derives the archimedean semi-local theory from
`ArchimedeanFactorizationStatement`. It defines and proves two conditional propositions.

## Statements

**`RankinSelbergGlobal.realPlaceFunctionalEquation_of_uniformContinuation`** is a theorem of
type `RealPlaceFunctionalEquationStatement.{u}`. This is the archimedean Rankin–Selberg
functional equation at the real places in both ranks (unequal ranks `t < r` and equal ranks).
It is defined in `Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement`, whose
Markdown gives the conventions (Jacquet 2009, Theorem 2.1 (i)–(iii)). It has no premises.

**`RankinSelbergGlobal.archimedeanSemilocalTheory_of_factorization`** derives
`ArchimedeanSemilocalTheoryStatement.{u, uQ}` from `ArchimedeanFactorizationStatement.{u, uQ}`.
The semi-local theory is the conjunction of the archimedean functional equations at all
infinite places, the factorization and the central sign.

**`CuspidalPairFunctionalEquationFactorizationStatement.{u, uQ}`** (namespace
`Langlands.Global`) is the implication

`ArchimedeanFactorizationStatement.{u, uQ} → CuspidalPairGlobalFunctionalEquationStatement.{u, uQ}`.

`cuspidalPairFunctionalEquationFactorization` proves it.

**`CuspidalPairPoles.CuspidalPairPoleFactorizationInputsStatement.{u, uQ}`** is the
implication

`ArchimedeanFactorizationStatement.{u, uQ} → RealOrdinaryNormalizedContinuationStatement →
RealOrdinaryNormalizedGenerationStatement → CuspidalPairPoleStatement.{u, uQ}`.

`cuspidalPairPoleFactorizationInputs` proves it. The pole proposition is defined in
`Langlands.Global.Factors.CuspidalPairPoleStatement`. The two real statements are defined in
`Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests` and are premises of
`CuspidalPairPoleGapGrowthInputsStatement` (module `CuspidalPairPoleGapGrowthReduction`).
`RealOrdinaryNormalizedContinuationStatement` says that every real ordinary unequal-rank and
equal-rank test has an entire normalization by the real pair `L`-factor
(`HasEntireOrdinaryNormalizations`). `RealOrdinaryNormalizedGenerationStatement` concerns block
lists with irreducible standard modules and nonzero Whittaker models. For them, and for every
nonzero real `a`, it says that at every point some normalized value is nonzero
(`HasCoveringOrdinaryNormalizations`). For equal ranks and for adjacent ranks `r = t + 1`, and
only when `a = 1` or `a = -1`, it also gives one finite family of normalized functions whose sum
is identically one on the whole plane (`HasFiniteOrdinaryNormalizationSum`).

## Proofs

All proofs are compositions of Library theorems. No new analysis is done here.

`realPlaceFunctionalEquation_of_uniformContinuation`. The Library's
`realPlaceUniformContinuationReduction` derives `RealPlaceFunctionalEquationStatement` from
three statements, and the proof supplies a proof of each:

- `RealLocalUniformUnequalContinuationStatement`: `realLocalUniformUnequalContinuation`;
- `RealLocalUniformPositiveEqualContinuationStatement`:
  `realLocalUniformPositiveEqualContinuation`;
- `RealPlaceContragredientPairLStatement`: `realPlaceContragredientPairLReduction` applied to
  `Automorphic.cuspidalArchimedeanStandardIrreducible` and to
  `realStandardPairingPairLReduction realStandardDualPairing realStandardIntertwinerPairL`.

`archimedeanSemilocalTheory_of_factorization`. The complex-place functional equation is
`complexPlaceFunctionalEquationLocalFEReduction` applied to
`complexLocalUnequalFunctionalEquation` and `complexLocalEqualFunctionalEquation`. The
real-place one is the theorem above, and the central sign is `archimedeanCentralSign`. The
factorization is the premise.

`cuspidalPairFunctionalEquationFactorization`. From the semi-local theory:

1. `unequalSemilocalArchimedeanReduction` gives `UnequalSemilocalEquationStatement`.
2. `equalSemilocalFactorization_of_archimedeanSemilocalTheory` followed by
   `equalSemilocalReduction` gives `EqualSemilocalEquationStatement`.
3. `cuspidalPairPartialGammaGlobalReduction` turns these two and eight proved global theorems
   into `CuspidalPairPartialGammaEquationStatement`. The eight are, in unequal ranks,
   `UnequalAnalytic.unequalAnalyticStatement_proof`, `unequalUnfoldingStatement_proof`,
   `unequalEulerFactorization` and `unequalDualEulerFactorization`, and, in equal ranks,
   `EqualAnalytic.equalAnalyticStatement_proof`, `equalUnfoldingStatement_proof`,
   `equalEulerFactorization` and `equalDualEulerFactorization`. They give analytic
   properties, unfolding, Euler factorization and dual Euler factorization.
4. `cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma` combines this with the
   Satake bound and gives `CuspidalPairCompletedEquationStatement`. The bound is
   `cuspidalSatakeBoundReduction` applied to
   `Automorphic.OperatorRealization.irreducibleCentralCharacter`.
5. `cuspidalPairFunctionalEquationReduction` combines the completed equation with
   `cuspidalPairLocalData` and `cuspidalArchimedeanParameterExistence` and gives the target.

`cuspidalPairPoleFactorizationInputs` applies the Library's `cuspidalPairPoleGapGrowthInputs`
to these arguments:

- the global functional equation obtained above;
- the two real premises;
- `complexOrdinaryNormalizedGeneration`;
- `infiniteWhittakerSliceModel`;
- `realPlaceWhittakerRestrictionSurjectivity` and
  `complexPlaceWhittakerRestrictionSurjectivity`;
- `realWhittakerModelUniformity`;
- `RealJacquet.realLocalUnequalCharacterGrowth_gap`, the real character-list growth at rank
  gaps of at least two.

## Provenance

This is an internal composition of Library results. It follows the proof of Theorem 4.1 in
J. W. Cogdell, *Analytic theory of L-functions for GL_n*, chapter 9 of Bernstein and Gelbart,
eds., *An Introduction to the Langlands Program*, Birkhäuser, 2004 (printed pp. 219–220).
That proof unfolds the global integrals, factors them into local integrals over `S` and the
infinite places, and applies the local functional equations at those places. The
archimedean factorization premise is that factorization step. The real-place functional
equation is Theorem 2.1 of H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009,
author-posted edition, p. 6). The pole proposition follows the route of Cogdell's
Theorems 4.1–4.2 (printed pp. 219–222), as in the Library's `cuspidalPairPoleFromLocalTests`
and `cuspidalPairPoleGapGrowthInputs`.

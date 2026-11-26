# Real ordinary strip growth from model uniformity and unequal growth at rank gaps of at least two

This module reduces the real ordinary strip growth needed by the cuspidal pair pole
construction to two premises. The first is the comparison of the real Whittaker coefficient
spaces with their uniform versions. The second is real character-list growth for pairs of
ranks that differ by at least two. It also states the corresponding form of the pole theorem.

## Statements

Throughout, the rank indices are `r` and `t`, and the groups are `GL(r + 1, ℝ)` and
`GL(t + 1, ℝ)`.

The two lemmas `realOrdinaryUnequalTest_stripGrowth_of_characterList` and
`realOrdinaryEqualTest_stripGrowth_of_characterList` concern one fixed pair of ranks. Assume
`RealWhittakerModelUniformityStatement` and real character-list growth at the pair:
`RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h` for `t < r`, or
`RealJacquet.RealLocalEqualCharacterGrowthAtRank r` for equal ranks. Then every entire
normalization of a real ordinary test (`realOrdinaryUnequalTest h d e a D`, respectively
`realOrdinaryEqualTest r d e a D`) by the real pair `L`-factor `realPairLFactor d e` has
exponential strip growth (`HasOrdinaryNormalizationStripGrowth`). This holds for all real block
lists `d`, `e` of total ranks `r + 1` and `t + 1` (respectively `r + 1` and `r + 1`), every
nonzero real `a` and every compatible quotient measure datum `D`.

`RankinSelbergGlobal.RealOrdinaryStripGrowthGapStatement` is the implication from

1. `RealWhittakerModelUniformityStatement`: `realWhittakerModel r ds a` is contained in
   `realUniformWhittakerModel r ds a` when `realRank ds = r + 1`, and
2. `RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h` for all `t < r` with
   `t + 1 < r`: for real character lists of total ranks `r + 1` and `t + 1` and functions in
   their uniform coefficient spaces with the characters `a` and `-a`, the unequal-rank integral
   and its dual form a normalized pair with exponential strip growth
   (`HasRealPairNormalizedGrowth`),

to `CuspidalPairPoles.RealOrdinaryNormalizedStripGrowthStatement`. That statement says that every
entire normalization of every real ordinary unequal-rank and equal-rank test, for the quotient
measures `realQuotientMeasureData`, has exponential strip growth. `realOrdinaryStripGrowthGap`
proves the implication. Premise 2 is not required at adjacent ranks `r = t + 1` or at equal
ranks.

`CuspidalPairPoles.CuspidalPairPoleGapGrowthInputsStatement.{u,uQ}` is the implication to
`CuspidalPairPoleStatement.{u,uQ}` from the following premises:

- `CuspidalPairGlobalFunctionalEquationStatement.{u,uQ}`;
- `RealOrdinaryNormalizedContinuationStatement`;
- `RealOrdinaryNormalizedGenerationStatement`;
- `ComplexOrdinaryNormalizedGenerationStatement`;
- `InfiniteWhittakerSliceModelStatement.{u,uQ}`;
- `RealPlaceWhittakerRestrictionSurjectivityStatement.{u}`;
- `ComplexPlaceWhittakerRestrictionSurjectivityStatement.{u}`;
- premises 1 and 2 above.

`cuspidalPairPoleGapGrowthInputs` proves it. The module proves none of the premises of the two
implications.

## Proofs

The two lemmas. Fix a test, that is, Whittaker functions `W` in `realWhittakerModel` for `d`
and `a` and `W'` for `e` and `-a` (and a Schwartz function in the equal-rank case). The
Library's `hasOrdinaryNormalizationStripGrowth_real_of_raw` reduces strip growth of every entire
normalization to the existence of a meromorphic function of exponential strip growth that
agrees with the test integral on a right half-plane. Premise 1 puts `W` and `W'` in the uniform
coefficient spaces. The Library's `RealJacquet.realUniformCharacterListInclusion` gives real
character lists `L`, `L'` of the same ranks whose uniform coefficient spaces contain those of
`d` and `e`. Character-list growth at `L`, `L'` gives a normalized pair, and the Library's
`RealJacquet.HasRealPairNormalizedGrowth.exists_meromorphic_stripGrowth` turns it into the
required meromorphic function: the entire normalization divided by the denominator of
`realPairLFactor L L'`. No comparison of `realPairLFactor L L'` with `realPairLFactor d e` is
needed.

`realOrdinaryStripGrowthGap`. Equal-rank character growth at every rank is the Library's
`RealJacquet.realLocalEqualCharacterGrowth_of_canonicalPremises`, applied to the proved
premises `RealUniformCanonicalRange.realUniformCanonicalRangePremise` and
`RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise`. At adjacent ranks
`r = t + 1`, unequal character growth is the Library's `RealJacquet.realAdjacentFromEqualGrowth`.
It is applied to the canonical range premise, to
`RealJacquet.realOrthogonalCompactProjectionPremise t` and to equal growth at rank index `t`.
For `t + 1 < r` it is premise 2. The two lemmas then give both conjuncts of the strip growth
statement, with `D = realQuotientMeasureData`.

`cuspidalPairPoleGapGrowthInputs` supplies `realOrdinaryStripGrowthGap` to the Library's
`cuspidalPairPoleRemainingInputs` (module `CuspidalPairPoleRemainingInputs`), together with the
remaining premises unchanged.

## Provenance

This is an internal reduction. It follows the induction on pairs of ranks in the proof of
Theorem 2.1 for principal series in H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009,
author-posted edition). The equal-rank and adjacent cases are §8.2 (p. 54) and §8.3
(pp. 58–60), which the Library proves through the modules named above. The pairs with rank gap
at least two, premise 2 here, are §9 (pairs `(n, n − 2)`, pp. 61–68) and §10 (pairs `(n, n′)`,
pp. 68–81). The passage from block lists to character lists replaces Jacquet's §11 (p. 81
onward) for the strip growth only. The reduction of strip growth to the existence of a
meromorphic continuation of exponential type is the Library's
`hasOrdinaryNormalizationStripGrowth_real_of_raw`. The global statement follows the route of
the Library's `cuspidalPairPoleFromLocalTests` (J. W. Cogdell, *Analytic theory of
L-functions for GL_n*, chapter 9 of Bernstein and Gelbart, eds., *An Introduction to the
Langlands Program*, Birkhäuser, 2004, §4, Theorems 4.1–4.2, printed pp. 218–222).

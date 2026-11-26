# Real ordinary continuation and strip growth from the uniform pair identities

This module gives a second reduction of the real ordinary local inputs of the cuspidal pair
pole construction, through Jacquet's pair identity instead of the normalized-growth induction,
and the corresponding form of the pole theorem.

## Statements

`RankinSelbergGlobal.RealOrdinaryNormalizedAllGrowthPairIdentityStatement` is the implication
from three premises to the conjunction of
`RankinSelbergGlobal.RealOrdinaryNormalizedContinuationStatement` (every real ordinary
unequal-rank and equal-rank test, for every compatible quotient measure, has an entire
normalization by the real pair `L`-factor) and
`CuspidalPairPoles.RealOrdinaryNormalizedStripGrowthStatement` (every such normalization, for
the quotient measures `realQuotientMeasureData`, has exponential strip growth). The premises are

1. `RealWhittakerModelUniformityStatement`: `realWhittakerModel r ds a` is contained in
   `realUniformWhittakerModel r ds a` when `realRank ds = r + 1`;
2. `RealLocalUniformUnequalPairIdentityStatement` and
3. `RealLocalUniformPositiveEqualPairIdentityStatement` (module
   `RealUniformPairIdentityReduction`): Jacquet's pair identity for the unequal-rank integrals
   and for the equal-rank integrals of positive rank index, on the uniform coefficient spaces,
   with the dual block lists, the parameter `-a` and the source determinant signs.

`CuspidalPairPoles.CuspidalPairPolePairIdentityPremisesStatement.{u,uQ}` is the implication from
`CuspidalPairGlobalFunctionalEquationStatement.{u,uQ}`, the real and complex ordinary generation
statements, `InfiniteWhittakerSliceModelStatement.{u,uQ}`, the real and complex restriction
surjectivity statements, and the three premises above, to `CuspidalPairPoleStatement.{u,uQ}`.

`realOrdinaryNormalizedAllGrowthPairIdentity` and `cuspidalPairPolePairIdentityPremises` prove
the two implications. The module proves none of the premises.

## Proofs

Unequal ranks. A test is a pair of Whittaker functions in `realWhittakerModel` for the lists
`d`, `e` and the characters `a`, `-a`. Premise 1 puts both in the uniform coefficient spaces.
The Library's `ArchimedeanRealPairIdentity.realUniformUnequalNormalization_of_pairIdentity`, with
premise 2, gives an entire normalization of the test integral by the reciprocal pair `L`-factor,
with exponential strip growth. The Library's `ordinaryNormalizationGrowthFromExistence`, with
nonvanishing of the pair denominator on a right half-plane
(`realPairLFactor_denominator_ne_zero`), turns one such normalization per test into existence of
entire normalizations and strip growth of every entire normalization.

Equal ranks. Rank index zero is the real half of the Library's `rankOneOrdinaryStripGrowth`,
which treats every test of `realWhittakerModel` directly. For positive rank index the argument
is that of the unequal case with
`ArchimedeanRealPairIdentity.realUniformPositiveEqualNormalization_of_pairIdentity` and
premise 3.

The continuation conclusion is obtained for every quotient measure datum and the strip growth
conclusion is the specialization to `realQuotientMeasureData`.

`cuspidalPairPolePairIdentityPremises` supplies both real conclusions to
`cuspidalPairPoleRemainingInputs` (module `CuspidalPairPoleRemainingInputs`).

## Provenance

This is an internal reduction. The pair identity and the deduction of entire normalizations of
exponential type in vertical strips from it are Jacquet's §4, H. Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §4.2 (definition of `(σ, ψ)` pairs, author-posted p. 22) and
Proposition 4.1 (p. 23), applied to the integrals (2.4) and (2.6) of Theorem 2.1 (p. 6). The
Library proves that deduction as `realPairIdentityNormalizedStripGrowth`; this module only
combines it with the model comparison and the rank-zero case. The global statement follows the
route of the Library's `cuspidalPairPoleFromLocalTests` (Cogdell 2004, §4, Theorems 4.1–4.2).

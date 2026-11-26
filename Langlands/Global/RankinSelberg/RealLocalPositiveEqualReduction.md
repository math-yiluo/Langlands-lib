# The real positive equal-rank continuation from the canonical premises

This module reduces `RealLocalUniformPositiveEqualContinuationStatement`, the meromorphic
continuation and local functional equation of the real equal-rank integrals at every positive
rank index, to two statements about canonical Jacquet maps of the Library:

- `RealGodement.RealUniformCanonicalRangePremise`: for every rank, `a ∈ ℝˣ`, parities `p` and
  exponents `z`, the uniform real Whittaker model `realUniformWhittakerModel r
  (characterList p z) (−a)` lies in the range of the canonical Jacquet map
  `RealGodement.canonicalJacquetMap a p z`;
- `RealGodement.RealCanonicalStandardEvaluationPremise`: for the same data there is a continuous
  linear form `L` on the smooth vectors of the Banach standard representation
  `RealStandardCompactBanach.representation` of `characterList p z` that is a Whittaker standard
  evaluation for `canonicalJacquetMap a p z` with character `−a`
  (`RealStandardCompactBanach.IsWhittakerStandardEvaluation`).

This module does not prove these two statements; they are the hypotheses of its results.

## Results

- `realLocalEqualCharacterGrowth_of_canonicalPremises`: given the two premises,
  `RealLocalEqualCharacterGrowthAtRank r` holds for every `r`.
- `RealLocalUniformPositiveEqualContinuationCanonicalPremisesStatement` is the implication
  `RealUniformCanonicalRangePremise → RealCanonicalStandardEvaluationPremise →
  RealLocalUniformPositiveEqualContinuationStatement`, and
  `realLocalUniformPositiveEqualContinuation_of_canonicalPremises` proves it.

## Proofs

The equal-rank character growth is proved by induction on `r`. Rank `0` is
`realLocalEqualCharacterGrowthAtRank_zero`. For the step from `t` to `t+1`,
`RealGodement.realLocalEqualGrowthStep t` takes the two canonical premises, the matrix
coefficient equation `RealGodement.realMatrixCoefficientGrowth t` of
`RealMatrixCoefficientGrowth`, and the adjacent-rank growth
`RealLocalAdjacentCharacterGrowthAtRank t`. The adjacent-rank growth is
`realAdjacentFromEqualGrowth` of `RealAdjacentCanonical`, applied to the canonical range premise,
the compact projection `realOrthogonalCompactProjectionPremise t` of
`RealOrthogonalCompactProjection` and the induction hypothesis.

The target then follows from
`realLocalUniformPositiveEqualContinuation_of_equalCharacterGrowth` of
`RealUniformTailInclusion`, which derives it from the equal-rank character growth at every
positive rank.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, proves Theorem 2.1(ii)–(iii) (p. 6) for the pairs
`(n, n)` and `(n, n − 1)` by a joint induction on `n` (§8.2, pp. 54–58, and §8.3, pp. 58–60): the
pair `(n − 1, n − 1)` gives `(n, n − 1)`, and together with Proposition 4.4 (§4.7, p. 31) this
gives `(n, n)`. The induction above follows this order for character lists. The passage from
character lists to general block lists is `RealUniformTailInclusion`.

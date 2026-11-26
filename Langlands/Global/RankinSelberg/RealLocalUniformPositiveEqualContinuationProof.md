# The real positive equal-rank continuation and local functional equation

`realLocalUniformPositiveEqualContinuation` proves
`RealLocalUniformPositiveEqualContinuationStatement` of `RealUniformContinuationReduction`. For
every positive rank index `r`, real block lists `ds`, `es` of total rank `r+1`, `a ∈ ℝˣ`,
compatible real quotient measure data `D` of rank `r`, functions `W` in
`realUniformWhittakerModel r ds a` and `W'` in `realUniformWhittakerModel r es (−a)`, and a row
Schwartz test `Φ`, it gives the package `RealJacquet.EqualContinuation a (−a) D W W' Φ ds es`
with the blockwise dual lists `ds.map RealLocalJacquet.dualBlock`,
`es.map RealLocalJacquet.dualBlock` and the sign `det(ds, −1)^r`. Thus `realEqualIntegral` and
`realEqualDualIntegral` have meromorphic continuations that agree with them on a common right
half-plane. Off a discrete set (on the codiscrete filter) the continuations satisfy the
multiplied-out local functional equation with the reciprocal denominators of
`realPairLFactor ds es` and of the pair of dual lists, the epsilon factor
`realPairEpsilon ds es (−a) √|a|` and the sign `det(ds, −1)^r`.

## Proof

The theorem applies `RealJacquet.realLocalUniformPositiveEqualContinuation_of_canonicalPremises`
of `RealLocalPositiveEqualReduction` to two theorems of `RealUniformCanonicalRange`:

- `RealUniformCanonicalRange.realUniformCanonicalRangePremise`, which proves
  `RealGodement.RealUniformCanonicalRangePremise`: for a real character list `characterList p z`,
  the uniform model `realUniformWhittakerModel r (characterList p z) (−a)` lies in the range of
  the canonical Jacquet map `RealGodement.canonicalJacquetMap a p z`;
- `RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise`, which proves
  `RealGodement.RealCanonicalStandardEvaluationPremise`: every canonical Jacquet map has a
  continuous Whittaker evaluation on the smooth vectors of the Banach standard representation.

The reduction theorem proves equal-rank character-list growth
`RealJacquet.RealLocalEqualCharacterGrowthAtRank r` at every rank by induction. Rank `0` is
`RealJacquet.realLocalEqualCharacterGrowthAtRank_zero`. The step from `t` to `t+1` is
`RealGodement.realLocalEqualGrowthStep t`. It takes as inputs the two canonical premises, the
matrix coefficient equation `RealGodement.realMatrixCoefficientGrowth t` and the adjacent-rank
growth at rank `t`. The adjacent-rank growth is `RealJacquet.realAdjacentFromEqualGrowth`, given
the canonical range premise, compact projection along the orthogonal group
(`RealJacquet.realOrthogonalCompactProjectionPremise t`) and the induction hypothesis.
`RealJacquet.realLocalUniformPositiveEqualContinuation_of_equalCharacterGrowth` of
`RealUniformTailInclusion` then passes from character lists to arbitrary block lists. It does so
through the inclusion of each uniform model of a block list into the model of a character list
that is a permutation of its expanded list, and gives the target.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, Theorem 2.1(ii)–(iii), p. 6, for the pair `(n, n)`
with `n = r + 1 ≥ 2`. Jacquet proves it in §8.2–8.3, pp. 54–60, by a joint induction with the
pair `(n, n − 1)`, and extends it from principal series to all generic representations in §11.
The target gives meromorphic continuation and the functional equation. Theorem 2.1(ii)
additionally expresses each meromorphic integral as a holomorphic multiple of its Langlands
`L`-factor and bounds the meromorphic integral at infinity in vertical strips; the target does
not include these assertions.

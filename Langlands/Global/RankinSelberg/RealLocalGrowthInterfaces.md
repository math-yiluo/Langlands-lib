# Rank-indexed normalized-growth statements for the real induction

This module fixes the interface between the equal-rank and unequal-rank parts of the real
normalized-growth induction. Both parts use the predicate
`RealJacquet.HasRealPairNormalizedGrowth` from `RealLocalNormalizedGrowth`. The definitions
mirror the complex `ComplexJacquet.ComplexLocalEqualGrowthAtRank` (module
`ComplexLocalEqualGrowthStep`). They also mirror the complex unequal predicate
`ComplexLocalUnequalGrowthAtRanks` of the unequal-rank proof (module `ComplexUnequalGrowthInduction`).

## Definitions

`RealLocalEqualGrowthAtRank r` has these inputs:

- real block lists `ds`, `es` of real rank `r + 1`;
- a real unit `a` and real quotient measure data `D` at rank `r`;
- `W` in `realUniformWhittakerModel r ds a` and `W'` in `realUniformWhittakerModel r es (-a)`;
- a Schwartz test `Φ` on `ℝ^(r+1)`.

It asserts that `realEqualIntegral D W W' Φ` and `realEqualDualIntegral (-a) D W W' Φ` satisfy
`HasRealPairNormalizedGrowth` with:

- dual lists `ds.map dualBlock`, `es.map dualBlock`;
- epsilon parameter `-a` and scale `sqrt |a|`;
- sign `det(ds, -1) ^ r`.

These are exactly the parameters of `RealLocalUniformPositiveEqualContinuationStatement`.

`RealLocalUnequalGrowthAtRanks r t h`, for `h : t < r`, has these inputs:

- lists `ds`, `es` of real ranks `r + 1` and `t + 1`;
- a real unit `a` and quotient measure data `D` at rank `t`;
- `W` in `realUniformWhittakerModel r ds a` and `W'` in `realUniformWhittakerModel t es (-a)`.

It asserts `HasRealPairNormalizedGrowth` for `realUnequalIntegral h D W W'` and
`realUnequalDualIntegral h a D W W'` with:

- the same dual lists, epsilon parameter and scale;
- sign `det(ds, -1) ^ (t + 1) · det(es, -1)`.

These are exactly the parameters of `RealLocalUniformUnequalContinuationStatement`.

`RealLocalAdjacentGrowthAtRank r` is the unequal statement at ranks `r + 1` and `r`.

## Theorems

- `realLocalEqualGrowthAtRank_zero` is `realLocalEqualRankZeroGrowth` from
  `RealLocalEqualRankZeroGrowth`, whose statement is literally `RealLocalEqualGrowthAtRank 0`.
- `realLocalUniformUnequalContinuation_of_growth`: unequal growth at every pair of ranks implies
  `RealLocalUniformUnequalContinuationStatement`. For each pair it applies
  `HasRealPairNormalizedGrowth.unequalContinuation`, which divides the entire normalizations by
  the reciprocal `L`-factors.
- `realLocalUniformPositiveEqualContinuation_of_growth`: equal growth at every positive rank
  implies `RealLocalUniformPositiveEqualContinuationStatement`, by
  `HasRealPairNormalizedGrowth.equalContinuation`.

## Provenance

These are internal statements organizing the induction in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §§8–10. The induction proves Theorem 2.1 (ii)–(iii) for equal and unequal
ranks together. The growth condition is exponential in `|Im s|` on vertical strips, which is
weaker than Jacquet's boundedness at infinity in vertical strips. The two predicates claim
nothing by themselves; only the theorems listed above are proved here.

# The real unequal-rank continuation and local functional equation

`realLocalUniformUnequalContinuation` proves `RealLocalUniformUnequalContinuationStatement`: for `t < r`,
block lists of total ranks `r+1` and `t+1`, `a ∈ ℝˣ`, compatible quotient measure data and functions of
`realUniformWhittakerModel r ds a` and `realUniformWhittakerModel t es (−a)`, the original
`realUnequalIntegral` and the dual block integral `realUnequalDualIntegral` have meromorphic continuations
agreeing with them on a right half-plane and satisfying the multiplied-out functional equation with the
inverse block lists, epsilon parameter `−a`, scale `√|a|` and sign `det(ds,−1)^(t+1) det(es,−1)` off a
discrete set (`RealJacquet.UnequalContinuation`). This is the continuation and functional-equation part of
Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1(ii)–(iii), p. 6, for real places.

## Proof

All results below are in `Langlands.Global.RankinSelbergGlobal.RealJacquet`.

* `realLocalAdjacentCharacterGrowth`: adjacent-rank character growth at every rank, from
  `realAdjacentFromEqualGrowth` with `realUniformCanonicalRangePremise`, `realOrthogonalCompactProjectionPremise`
  and the equal-rank growth `realLocalEqualCharacterGrowth_of_canonicalPremises` (with
  `realCanonicalStandardEvaluationPremise`).
* `realLocalUnequalCharacterGrowth_gap`: for `t + 1 < r`, `RealLocalUnequalCharacterGrowthAtRanks r t h`;
  `realLocalUnequalCharacterGrowth`: the same for every `t < r`. Both follow by induction on `q` in
  `r = t + 1 + q`: the case `q = 0` is the adjacent growth and the successor case is
  `RealGapCanonicalGrowth.realGapGrowthStep`.

The theorem is the Library's `realLocalUniformUnequalContinuation_of_unequalCharacterGrowth` applied to
`realLocalUnequalCharacterGrowth`. That reduction includes the uniform coefficient space of each block list
in the uniform coefficient space of a character list that is a permutation of its expansion into characters
(`realUniformCharacterListInclusion`, at `a` for `ds` and at `−a` for `es`). It applies the character-list
growth to the same two functions `W`, `W'`, which gives their continuation package for the character lists
(`HasRealPairNormalizedGrowth.unequalContinuation` turns the normalized growth into the continuation package).
It then transports the pair L-factors, the epsilon factor and the sign back to the
original block lists (`determinant_perm`, `determinant_expand`, `realPairLFactor_perm`,
`realPairEpsilon_perm` and `continuationPackage_of_expand`).

Jacquet proves the rank induction for principal series in §§8–10 of *Archimedean Rankin–Selberg integrals*
(2009): equal and adjacent ranks in §8, pp. 52–61, rank difference two in §9, pp. 61–68, and the recurrence
for rank differences greater than two in §10, pp. 68–81. The Lean step `realGapGrowthStep` holds for every
`q`, so its case `q = 0` gives rank difference two as well; no separate argument corresponding to §9 is
used.

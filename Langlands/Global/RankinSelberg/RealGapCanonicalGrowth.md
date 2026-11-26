# The real normalized larger-gap equation for every inducing parameter

* `tailWeyl_mem_unitary`: the tail reversal `blockSum (1, w_(q+2))` is orthogonal.
  `translate_godementCoefficient`: right translation by it of the split Godement coefficient of a Gaussian
  monomial test and a column test `φ` is `rotatedValue` of the split factors `gaussianFactors`.
* `realGapChamberGrowth`: assume `RealLocalUnequalCharacterGrowthAtRanks (t+1+q) t`. For `Z` in the strict
  chamber with the Godement convergence bound on the leading exponent, `B` a uniform intertwiner of
  `fs.map character` at `a` and every vector `F`, the canonical value `canonicalJacquetMap a P Z F` lies in
  `unequalGrowthSubmodule (rankLT t (q+1)) D (−a) (B v)` for the lists `characterList P Z`, `fs`, their duals,
  the epsilon parameter `a`, the scale `√|a|` and the sign `det(characterList P Z, −1)^(t+1) det(fs, −1)`.
* `realGapCanonicalGrowth`: under the same hypothesis, for `B` at `−a`, `HasRealUnequalCanonicalPairGrowth`
  holds for every inducing parameter `Z`.
* `RealGapGrowthStepStatement` (proved by `realGapGrowthStep`): `RealLocalUnequalCharacterGrowthAtRanks (t+1+q) t`
  implies `RealLocalUnequalCharacterGrowthAtRanks (t+1+q+1) t`.

## Proof

The canonical map commutes with right translation by the orthogonal group, and the tail reversal is an
involution (`tailWeyl_mul_self`), so a canonical value is the tail-reversed canonical value of a translated
vector. By `canonicalJacquetMap_mem_span_monomialSplitGenerators` the latter lies in the span of monomial
split generators, whose tail reversals are the rotated values of `realGapMonomialGrowth`; these satisfy the
normalized equation, and they lie in the uniform model (`translate_mem_model`), so `realUnequalPairConvergence`
gives the convergence required by `unequalGrowthSubmodule`. Since the submodule is closed under spans, this
proves `realGapChamberGrowth`.

`realChamberRemoval` with `realUnequalCanonicalGrowthReflection` removes the chamber and the bound on the
leading exponent (the sign depends only on the parities, `determinant_characterList_neg_one`). For the step,
`exists_characterList_eq` writes both character lists as `characterList`, and
`realUniformCanonicalRangePremise` writes both model functions as canonical values; the smaller canonical map
is a uniform intertwiner at `−a` (`realGodementCanonicalModel`).

This is the induction on the rank difference in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10,
p. 68, for principal series of characters, with the continuation in the inducing parameters. Jacquet runs
that induction for rank differences greater than two and treats rank difference two in §9, pp. 61–68; the
step here holds for every `q`, so its case `q = 0` also gives rank difference two.

# Real ordinary normalized strip growth from character-list growth

This module reduces `Langlands.Global.CuspidalPairPoles.RealOrdinaryNormalizedStripGrowthStatement`
(module `Langlands.Global.Factors.CuspidalPairPoleFromLocalTests`) to named premises. That
statement says: for the ordinary unequal-rank and equal-rank real Rankin–Selberg tests
`realOrdinaryUnequalTest` and `realOrdinaryEqualTest`, with the compatible quotient measures
`realQuotientMeasureData`, every entire normalization by the real pair `L`-factor
`realPairLFactor d e` has exponential growth in vertical strips (`HasStripExponentialGrowth`).
The tests take their Whittaker functions in `realWhittakerModel`.

## The two reductions

`RealOrdinaryStripGrowthCharacterReductionStatement` is the implication from four premises to
the strip growth statement:

1. `RealWhittakerModelUniformityStatement` (module `RealWhittakerModelUniformityStatement`):
   `realWhittakerModel r ds a ≤ realUniformWhittakerModel r ds a` whenever
   `realRank ds = r + 1`;
2. `RealUniformPrincipalSeriesInclusionStatement` (module `RealPrincipalSeriesReduction`): the
   uniform coefficient space of a block list lies in that of its expansion `expand ds`, a list
   of real characters of the same rank;
3. `RealJacquet.RealLocalUnequalCharacterGrowthAtRanks r t h` for all `t < r`;
4. `RealJacquet.RealLocalEqualCharacterGrowthAtRank r` for all `r > 0`.

The last two (module `RealLocalCharacterGrowthInterfaces`) assert the normalized form
`RealJacquet.HasRealPairNormalizedGrowth` of the unequal and equal integrals for two lists of
real characters and Whittaker functions in the uniform coefficient spaces: entire functions of
exponential strip growth that equal the reciprocal pair `L`-factor times the integrals on a
right half-plane and satisfy the normalized functional equation. Rank index zero of the equal
statement is the Library's `RealJacquet.realLocalEqualCharacterGrowthAtRank_zero`.

`RealOrdinaryStripGrowthPremisesStatement` replaces premise 4 by the three premises of the real
equal-rank successor step of module `RealLocalEqualGrowthStep`:
`RealGodement.RealUniformCanonicalRangePremise`,
`RealGodement.RealCanonicalStandardEvaluationPremise` and
`RealGodement.RealMatrixCoefficientGrowthPremise t` for every `t`. Its premises are therefore
premises 1–3 and these three.

`realOrdinaryStripGrowthCharacterReduction` and `realOrdinaryStripGrowthPremises` prove the two
implications. None of the premises is proved in this module.

## Supporting results

In namespace `Langlands.LocalFactor.Archimedean`:

- `stripGrowth_Gamma`: `Complex.Gamma` is bounded on every closed vertical strip for
  `|Im s| ≥ 1`. Choose `n` with `a + n > 0`. For `|Im s| ≥ 1` each `|s + k|` is at least one,
  so the recursion `Γ(s + 1) = s Γ(s)` gives `‖Γ(s)‖ ≤ ‖Γ(s + n)‖`. The Library's
  `norm_Gamma_le_on_strip` bounds `Γ` on the shifted strip, which lies in the right half-plane.
- `stripGrowth_Gammaℝ`, `stripGrowth_Gammaℂ`: the factors `π^(-s/2) Γ(s/2)` and
  `2 (2π)^(-s) Γ(s)` have exponential strip growth. The powers `p^(-s)` with `p ≥ 1` have
  modulus `p^(-Re s)`, bounded on each strip; `HasStripExponentialGrowth.div_add` handles the
  argument `s/2` and `HasStripExponentialGrowth.mul` the products.
- `GammaBlock.stripGrowth_inv_denominator`, `stripGrowth_gammaProduct_inv_denominator` and
  `stripGrowth_realPairLFactor_inv_denominator`: the reciprocal of the denominator of a shifted
  Gamma block is the shifted Gamma factor itself, so it has exponential strip growth; so does a
  finite product of them, and hence the real pair `L`-factor
  `((realPairLFactor xs ys).denominator s)⁻¹`, via `realLFactor_eq_gammaProduct`.

In namespace `Langlands.Global.RankinSelbergGlobal`:

- `RealJacquet.HasRealPairNormalizedGrowth.exists_meromorphic_stripGrowth`: if `I` has a real
  normalized pair with entire normalization `N`, then `M = N · (pair denominator)⁻¹` is
  meromorphic on `ℂ`, has exponential strip growth (product of the growth of `N` and of the pair
  `L`-factor), and equals `I` on a right half-plane on which the denominator does not vanish
  (`realPairLFactor_denominator_ne_zero`).
- `realOrdinaryUnequalTest_stripGrowth`, `realOrdinaryEqualTest_stripGrowth`: strip growth for
  every quotient measure datum, from premises 1–2 and the character growth at the given ranks.

## Proof of the reductions

Fix a test, that is Whittaker functions `W`, `W'` (and in equal rank a Schwartz function) in
`realWhittakerModel` for the lists `d`, `e` and the characters `a`, `-a`. Premise 1 puts `W` and
`W'` in the uniform coefficient spaces of `d` and `e`, and premise 2 in those of `expand d` and
`expand e`. These are character lists (`RealJacquet.isRealCharacterList_expand`) of the same
ranks (`realRank_expand`). Character growth for the expanded lists gives the normalized pair of
the same integral, normalized by the expanded pair factor. By
`exists_meromorphic_stripGrowth` the integral agrees on a right half-plane with a meromorphic
function of exponential strip growth. The Library's
`hasOrdinaryNormalizationStripGrowth_real_of_raw`, through
`OrdinaryIntegralNormalization.stripGrowth_realPair`, then gives exponential strip growth of
every entire normalization of the test by the original pair factor `realPairLFactor d e`. No
comparison of the original and expanded normalizations is needed: an entire normalization by the
original factor agrees on a right half-plane with the meromorphic continuation times the original
denominator, and the identity theorem extends the strip bound of that product to it.

For `RealOrdinaryStripGrowthPremisesStatement`, each positive rank is `t + 1`, and the Library's
`RealGodement.realLocalEqualGrowthStep t` gives equal character growth at rank `t + 1` from the
three successor-step premises and the adjacent character growth
`RealLocalAdjacentCharacterGrowthAtRank t`, which is premise 3 at the ranks `t + 1` and `t`.

## Provenance

This is an internal reduction for the real ordinary local inputs of the cuspidal pair pole
construction. The growth assertion corresponds to the boundedness in vertical strips in
H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1(ii), author-posted
version p. 6, in the weaker form of exponential growth in `|Im s|` used throughout the Library.
Jacquet proves his theorem for representations induced from characters by the induction of
§§8–10 (pp. 52–80) and passes to the general case in §11 (p. 81 onwards); the premises here follow the same order, with the
character-list growth statements as the induction's conclusion and the principal-series
inclusion as the passage to block lists. Only the meromorphic continuation with its strip bound
is used from the character-list statements; the holomorphy of the integral divided by the
original block factor is not needed for the strip bound.

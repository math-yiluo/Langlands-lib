# The normalized real unequal-rank equation is preserved by linear spanning

For `h : t < r`, a quotient measure datum `D`, a dual parameter `b`, a fixed smaller function `V` and the data
of `HasRealPairNormalizedGrowth`, `unequalGrowthSubmodule h D b V xs ys xsd ysd eb c hc sign` is the submodule
of functions `W` on `GL_(r+1)(ℝ)` for which there is `σ` with `realUnequalIntegrand h W V s` integrable for
`D.measure` and `realUnequalDualKernel h W V s` integrable for `realUnequalDualMeasure b D` whenever
`σ < Re s`, and `HasRealPairNormalizedGrowth xs ys xsd ysd eb c hc sign` holds for
`realUnequalIntegral h D W V` and `realUnequalDualIntegral h b D W V`.

Closure under addition and scalars uses that the integrand and the dual block kernel are linear in `W`
(`unequalIntegrand_add`, `unequalIntegrand_smul`, `dualKernel_add`, `dualKernel_smul`), that the dual
integral is the product integral of an integrable dual kernel (`dualIntegral_eq_prod`), and the closure of
the normalized growth package under sums, scalar multiples and agreement on a right half-plane
(`HasRealPairNormalizedGrowth.add`, `.const_mul`, `.congr`). This is the general-rank version of the Library's
`RealJacquet.adjacentGrowthSubmodule`.

`translate_mem_model`: right translation by an element of the orthogonal group `unitaryCompact ℝ (r+1)`
preserves `realUniformWhittakerModel r ds a`. A uniform intertwiner commutes with right translation by the
compact group, which preserves the compact-finite standard module
(`rightTranslation_mem_kFiniteFunctions_realStandardModule`).

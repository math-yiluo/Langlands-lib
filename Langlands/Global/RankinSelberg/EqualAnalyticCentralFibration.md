# Fibration of `GL_n(F) \ GL_n(𝔸)` over the centre

Module `Langlands.Global.RankinSelberg.EqualAnalyticCentralFibration`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Notation: `zeta F n a = a I_n` is the scalar embedding of `GL_1(𝔸)` in `GL_n(𝔸)`. `glRational F n`
is `GL_n(F)`, `glDomain F n` is its Library fundamental domain `D`, and
`glSlab F n = {g | 1 ≤ |det g| < e^n}` is `S`.

## The scalar embedding and the centre

- `zeta` is a continuous homomorphism with central values (`zeta_mul`, `zeta_inv`,
  `continuous_zeta`, `zeta_mul_comm`), and `|det(a g)| = |a|^n |det g|`
  (`detNorm_zeta_mul`, `log_detNorm_zeta_mul`).
- `exists_zeta_eq_of_mem_center`: every central element of `GL_n(𝔸)` is a scalar `ζ(a)`.
  This is Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`, transported along the
  Library isomorphism `GeneralLinearGroupPoints.adelicEquiv`.
- `centralRationalSubgroup_invariant`: a function invariant under `GL_n(F)` and under all
  `ζ(a)` is invariant under the subgroup `Z_n(𝔸) GL_n(F)` (`centralRationalSubgroup` of
  `EqualIntegrals`). The proof uses its stabilizer subgroup (`invariantSubgroup`).

## The fibration

- `ideleMeasure_fiber`: for every `g`, `{a ∈ D₁ | ζ(a)⁻¹ g ∈ S}` has `d^×a`-measure one. It is
  `D₁ ∩ {log |a| ∈ (L/n - 1, L/n]}` with `L = log |det g|`, of measure one by
  `ideleMeasure_logNorm_preimage`.
- **`rationalQuotientHaarMeasure_eq_map`**: the Library quotient measure on
  `GL_n(F) \ GL_n(𝔸)` is the image of `fibrationMeasure = μ|_(D ∩ S) ⊗ d^×a|_(D₁)` under
  `fibrationMap (g, a) = GL_n(F) ζ(a) g`. This combines `quotientMeasure_eq_map_fibration` with
  the Library identification `rationalQuotientHaarMeasure_eq`.
- Consequences: `lintegral_rationalQuotient_eq`, `integrable_rationalQuotient_iff` and
  `integral_rationalQuotient_eq`, giving
  `∫_(GL_n(F)\GL_n(𝔸)) f = ∫_(D ∩ S) ∫_(D₁) f(ζ(a) g) d^×a dg`.

## The central quotient

`centralQuotientMeasure F n` of `EqualIntegrals` is the image of `μ|_(D ∩ S)` under
`D ∩ S → Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` (`restrict_determinantSlab`,
`centralQuotientMeasure_eq_map`). For a strongly measurable function `f` invariant under
`Z_n(𝔸) GL_n(F)`, the function `q ↦ f(q.out)` is integrable for `centralQuotientMeasure` iff
`f` is integrable on `D ∩ S`, with the same integral (`integrable_centralQuotientMeasure_iff`,
`integral_centralQuotientMeasure`).

## Provenance

This is the decomposition `∫_(GL_n(F)\GL_n(𝔸)) = ∫_(Z_n(𝔸)GL_n(F)\GL_n(𝔸)) ∫_(F^×\𝔸^×)` used
implicitly in Cogdell 2004, §2.3, printed pp.208–209. The proofs are internal.
`glRational`, `glDomain`, `glSlab`, `fibrationMap`, `fibrationMeasure` and `invariantSubgroup`
are internal names.

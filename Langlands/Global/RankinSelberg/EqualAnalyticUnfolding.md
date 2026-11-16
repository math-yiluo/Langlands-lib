# Unfolding the equal-rank integral to the theta kernel

Module `Langlands.Global.RankinSelberg.EqualAnalyticUnfolding`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

For `P : GL_n(𝔸) → ℂ` and `Φ`, the theta kernel is
`thetaKernel F r P Φ s g = P(g) |det g|^s Θ(Φ, g)`, and
`thetaKernelNorm F r P Φ s g = |P(g)| ||det g|^s| Θ⁺(Φ, g)` is its majorant
(`enorm_thetaKernel_le`). Both are `GL_n(F)`-invariant for invariant `P`
(`thetaKernel_rational_mul`, `thetaKernelNorm_rational_mul`), and both transform under scalars
as `thetaKernel_zeta_mul` and `thetaKernelNorm_zeta_mul` describe. The section and the
Eisenstein series are strongly measurable (`stronglyMeasurable_eisensteinSection`, via
`StronglyMeasurable.integral_prod_right'`; `stronglyMeasurable_eisensteinSeries`, via
`StronglyMeasurable.tsum`).

## `equalIntegral_unfold`

Let `φ`, `φ'` be continuous and `GL_n(F)`-invariant with
`φ(a g) φ'(a g) = χ(a) φ(g) φ'(g)`, and let `Φ` be continuous. Suppose
`∫_(GL_n(F)\GL_n(𝔸)) K⁺_s < ∞`. Then the integrand of `equalIntegral F χ φ φ' Φ s` is integrable
for `centralQuotientMeasure`, and

`equalIntegral F χ φ φ' Φ s = ∫_(GL_n(F)\GL_n(𝔸)) P(g) |det g|^s Θ(Φ, g) dg`, with `P = φ φ'`.

Proof:

1. `f = φ φ' E` is invariant under `Z_n(𝔸) GL_n(F)`
   (`eisensteinSeries_rational_mul`, `eisensteinSeries_zeta_mul`,
   `centralRationalSubgroup_invariant`). So integrability and the integral for
   `centralQuotientMeasure` are those of `f` on `D ∩ S`
   (`integrable_centralQuotientMeasure_iff`, `integral_centralQuotientMeasure`).
2. Pointwise `|f(g)| ≤ ∫_(D₁) K⁺_s(ζ(a) g) d^×a` (`enorm_eisensteinSeries_le`), and the double
   integral is `∫ K⁺_s < ∞` by the fibration (`lintegral_rationalQuotient_eq`).
3. For almost every `g ∈ D ∩ S` the inner integral is finite. Then either `P(g) = 0`, or
   `eisensteinSeries_eq` applies, so `f(g) = ∫_(D₁) K_s(ζ(a) g) d^×a`.
4. The fibration (`integral_rationalQuotient_eq`) turns `∫_(D ∩ S) ∫_(D₁) K_s(ζ(a) g)` into
   `∫_(GL_n(F)\GL_n(𝔸)) K_s`.

## Provenance

This is the first step of the analysis of `I(s)` in Cogdell 2004, §2.3, printed pp.208–209:
replace the Eisenstein series by its theta-series expression and fold the integral over the
centre. The proof is internal. `continuous_lastRow`, `adelicEquiv_rational_mul` and
`glRational_invariant` are auxiliary.

# Joint convergence on the real determinant-one gap chart

This module is the real counterpart of the Library's `ComplexGapNormalizedWeighted`; `δ(g) = |det g|`.

* `quotientDetAbs_mk`, `quotientDetAbs_right`: the quotient determinant `quotientDetAbs` of
  `RealUnequalMellinReduction` at the class of `g` is `δ(g)`, and right translation by `S` multiplies it by
  `δ(S)`. `padGL_eq_rankInclusion` identifies padding with the leading block inclusion.
* `normalizedWeightedKernel dual a Φ₀ Φ Ψ Ξ W V s f₁ f₂ w v` is the split kernel on the normalized chart:
  with `B = unitRetained p` and `h` the leading matrix, the product of
  `Φ₀((leadingSide B) · leadingStack (leadingSide h) Y)`, `Φ` at the first tail column of `B`, `Ψ` at the last
  row of `B^{-1}`, `triangularFourier (t + 1) q a B Ξ Z`, `realUnequalIntegrand(ρ(B^{-1}) W, ρ(h) V, s)`,
  `f₁(quotientDetAbs)`, `f₂(δ(leadingSide h))` and `w(p)`.
* `normalizedGapMeasure t q a D νY η₁ κ` is `alternateGapMeasure` with `unitOuterMeasure` (the outer measure
  with the density `normalizationWeight`) in place of `outerMeasure`. On this chart the retained matrix
  `unitRetained p` has absolute determinant one (`normalizedAbs_unitRetained`), as the retained matrix in
  Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.2, pp. 73–74.

`RealGapNormalizedWeightedStatement` (proved by `realGapNormalizedWeighted`): under the hypotheses of
`RealGapAlternateWeighted` (measurable weights `f₁`, `f₂` with `RapidDecay`: for every real `M` there is
`C` with `‖f(x)‖ ≤ C x^M` for all `x > 0`, and `w` bounded by `C δ(leadingSide h)^β exp(b ∑|y_i|)`), the
normalized kernel is integrable for `normalizedGapMeasure`; `realGapNormalizedPowerBounds` is the version
with power bounds.

The proof pulls the kernel back along `normalizationShear`. Write `L = ∑ y_i` for the sum of the tail
logarithms and `S = leadingScalar y`. The shear translates the quotient variable on the right by `S` and
multiplies the leading variable on the left by `S^{-1}` after `leadingSide`. The scalar determinant is
`δ(S) = exp(−L)` (from `normalizedAbs_unitRetained` and `normalizedDet_retained`: the retained matrix has
absolute determinant `exp(L)`), and the Jacobian of the rescaled `k × q` rectangle is the density
`normalizationWeight y = δ(S)^q = exp(−qL)`. The normalized leading argument becomes the original one
(`realGapNormalizationColumns`). The scalar cancels in the Whittaker arguments and leaves the power
`|det S|^{s − (q+1)/2}` (`detPower` is multiplicative). The first determinant argument, the quotient
determinant, is rescaled by `exp(−L)`. The second, `δ(leadingSide h)`, is rescaled by `exp(L)` on the
ordinary side and by `exp(−L)` on the inverse-transpose side. The density and these rescalings fit the
fixed exponential allowed by `realGapAlternatePowerBounds`. In the complex module the scalar determinant
is `exp(−2L)` and the Jacobian `exp(−2qL)`, because the normalized complex absolute value is the square
of the modulus; here `δ` is the ordinary absolute value.

This is an internal step of the convergence and Mellin analysis of the larger-gap recurrence in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.

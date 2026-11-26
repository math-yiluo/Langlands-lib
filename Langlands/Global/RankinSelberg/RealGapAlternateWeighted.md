# Independent rapid determinant weights on the real alternate gap kernel

This module is the real counterpart of the Library's `ComplexGapAlternateWeighted`.

* `leadingSide dual g` is `g` or its inverse transpose.
* `ordinaryKernel_mk`: for `W`, `W'` with left characters `ψ_a`, `ψ_{−a}` (`RealUnequalFamily.HasLeftCharacter`),
  the Library's `realUnequalIntegrand` at the class of `g` is `W(diag(g, 1)) W'(g) |det g|^{s − (r − t)/2}`;
  `left_translate` keeps the left character under right translation; `leftCharacter_of_mem` and
  `continuous_of_mem` give the left character and continuity of vectors of `realUniformWhittakerModel`
  (from `realUniformWhittakerRegularity`).
* `weightedAlternateKernel dual a Φ₀ Φ Ψ Ξ W V s c₁ c₂ f₁ f₂ w v` is the product of
  `Φ₀((leadingSide B) · leadingStack z Y)`, `Φ(firstRetainedColumn p)`, `Ψ(lastRetainedInverseRow p)`,
  `triangularFourier (t + 1) q a B Ξ Z`, `realUnequalIntegrand(ρ(B^{-1}) W, ρ(leadingSide z) V, s)` at the
  quotient point, `f₁(e^{c₁ ∑ y} · quotientDetAbs)`, `f₂(e^{c₂ ∑ y} · δ(z))` and `w(p)`.

`RealGapAlternateWeightedStatement` (proved by `realGapAlternateWeighted`): for `W` in
`realUniformWhittakerModel (t + 1 + q) ds (−a)`, `V` in `realUniformWhittakerModel t es a`, Haar measures
`η₁`, `κ`, `νY` as in `RealGapAlternateConvergence`, measurable `f₁`, `f₂` that decay rapidly on the
positive axis (`ArchimedeanMellinPair.RapidDecay`: for every real `M` there is `C` with
`‖f(x)‖ ≤ C x^M` for all `x > 0`), and a measurable `w` with `‖w p‖ ≤ C δ(z)^β exp(b ∑|y_i|)` (`C, b ≥ 0`),
the kernel is integrable for `alternateGapMeasure`. The weights need not be continuous: the indicator
function of `[1, 2]` is measurable and satisfies `RapidDecay`. `realGapAlternatePowerBounds` gives the
same for weights bounded by independent powers above two thresholds.

The proof bounds the rapid weights by sufficiently large powers of their arguments; the exponential
rescalings and `w` fit into the fixed exponential of `realGapAlternateConvergence`, which applies with
`B₁ = leadingSide B` and `z₁ = leadingSide z` (inverse transpose preserves the height,
`RealJacquet.realMatrixHeight_inverseTranspose`). For measurability, the Schwartz factors, the triangular
Fourier factor, the Whittaker product descended to the quotient (evaluated by `ordinaryKernel_mk`) and the
two determinant arguments are continuous. Composing the measurable `f₁`, `f₂` and `w` with these
continuous maps gives a measurable kernel. The complex statement takes vectors of the complex Whittaker
models; here the vectors lie in the uniform real Whittaker models and `η₁` is any Haar measure.

This is an internal step of the convergence and Mellin analysis of the larger-gap recurrence in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.

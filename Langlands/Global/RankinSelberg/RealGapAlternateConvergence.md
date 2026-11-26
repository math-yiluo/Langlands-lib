# Joint absolute convergence in the alternate real gap chart

This module is the real counterpart of the Library's `ComplexGapAlternateConvergence`. Matrices carry the
operator norm; `δ(g) = |det g|` and `H` is the real matrix height.

* `alternateGapMeasure t q a D νY η₁ κ` is the product of the quotient measure `D.measure` on
  `N_{t+1} \ GL_{t+1}(ℝ)`, a measure `νY` on the lower `(q + 1) × (t + 1)` rectangle, the outer measure
  `outerMeasure (t + 1) q μ η₁ κ` of `RealGapTriangularChart` and the entry Haar measure of `N_{q+1}(ℝ)`,
  with `μ = realSelfDualMeasure a`.
* `alternateGapNorm a Φ₀ Φ Ψ Ξ W V u s b g z₁ B₁ Y p Z` is, with `B = retainedMatrix p` and `z` the leading
  matrix of `p`,
  `‖Φ₀(B₁ · leadingStack z Y)‖ ‖Φ(firstRetainedColumn p)‖ ‖Ψ(lastRetainedInverseRow p)‖
  ‖triangularFourier (t + 1) q a B Ξ Z‖ ‖W(diag(g, 1) B^{-1})‖ ‖V(g z₁)‖ δ(g)^u δ(z)^s exp(b ∑|y_i|)`.

`RealGapAlternateConvergenceStatement` (proved by `realGapAlternateConvergence`): let `W` and `V` satisfy
the simple-root gauge bound `HasGaugeBound`, let `η₁` be a Haar measure on `GL_{t+1}(ℝ)`, `κ` a Haar
measure on the orthogonal group, `νY` σ-finite with `matrixDecay l` integrable. There are `σ`, `τ` such
that the following holds for `u ≥ σ`, `s ≥ τ`, `b ≥ 0`, all Schwartz tests and `C ≥ 0`. Let `B₁` and `z₁` be
arbitrary functions of the outer coordinates `p` with `H(B₁ p) ≤ H(retainedMatrix p)` and `H(z₁ p) ≤ H(z)`
for every `p`; no measurability is required of them. Then every function `F` that is a.e. strongly
measurable for `alternateGapMeasure` and satisfies `‖F v‖ ≤ C · alternateGapNorm …` at every point, with
the norm evaluated at the chosen quotient representative `v.1.out`, is integrable for
`alternateGapMeasure`.

The proof bounds `W` by its gauge bound at the coordinate `append (alpha g) (−y)`
(`alpha_rankInclusion_mul_retained_inv`), `V(g z₁)` by `realWhittakerTranslateBound`, the leading test
by `realGapLeadingSchwartz`, and the rest by `realGapAlternateTailBound`. The toral density of `D.measure`
is given by `RealIwasawa.exists_lintegral_alphaQ`; the resulting product of integrable factors
(the quotient exponential, `matrixDecay l`, `weightedMatrixTail` for `η₁`, `diagonalDecay`, the
constant on `κ`, `headDecay` and `unipotentDecay`) dominates `F`.

The complex statement takes `W`, `V` in the complex Whittaker models and the explicit complex Haar
measure; here the gauge bounds suffice and `η₁` is any Haar measure. The thresholds are `σ = A + 1` and
`τ = (t + 1) + 2M` instead of `(A + 1)/2` and `(t + 1) + M`, because `δ` is the ordinary absolute value.

This is an internal step of the convergence and Mellin analysis of the larger-gap recurrence in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.

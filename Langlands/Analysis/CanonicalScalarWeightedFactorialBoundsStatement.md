# Actual weighted factorial derivative bounds for a scalar elliptic equation

`Langlands.Analysis.CanonicalScalarWeightedFactorialBoundsStatement d r` is a
`Prop`-valued statement. It is stated here and **not proved**; this module
contains no proof and does not assume any analytic estimate. The Lean statement
was written by Worker 94. Worker 881 revised this Markdown for precision and
provenance.

## Hypotheses

The statement is an implication with the following hypotheses, in this order.

- `0 < d` and `0 < r`: the dimension and the operator order are positive.
- `D : CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r` is an actual
  scalar operator of order `r` on real Euclidean space. Its basis is the
  canonical one: `D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis`. The
  space keeps its Euclidean norm and Lebesgue measure `volume`.
- `S` is an open subset of `EuclideanSpace ℝ (Fin d)`.
- `D.AnalyticCoefficientsOn S`: every actual coefficient
  `D.coefficient k w` (for every order `k ≤ r` and ordered word `w`) is real
  analytic at each point of `S` (`AnalyticOnNhd ℝ`).
- `D.IsEllipticOn S`: at each `x ∈ S`, the actual principal symbol
  `D.principalSymbol x ξ` is nonzero for every nonzero continuous real-linear
  covector `ξ`. This is pointwise ellipticity, not a uniform lower bound.
- `u : EuclideanSpace ℝ (Fin d) → ℂ` satisfies `ContDiffOn ℝ ∞ u S`. Only
  smoothness on `S` is assumed, not global smoothness.
- `∀ x ∈ S, D.action u x = 0`: `u` solves the actual full homogeneous
  equation on `S`, including all lower-order terms of `D`.

No estimate certificate is bundled into `D`. No regularity or equation
hypothesis replaces the actual coefficients or the actual full action.

## Conclusion

For every `x₀ ∈ S` and every real `R₀ > 0` there exist real numbers `R`,
`C`, `A` with

- `0 < R`, `R ≤ R₀`, and `Metric.closedBall x₀ R ⊆ S`;
- `0 < C` and `0 < A`;
- for every natural number `k`,

  `ballWeightedSeminorm (derivWordNorm k u) x₀ R k ≤ ENNReal.ofReal (C * A ^ k * (k ! : ℝ))`.

`R`, `C` and `A` are chosen after `x₀` and `R₀` but before `k`, so one radius
and one pair of constants serve every derivative order. They may depend on
`d`, `r`, `D`, `S`, `u`, `x₀` and `R₀`. Since the right side is finite, the
conclusion in particular makes every weighted seminorm finite.

The two quantities come from the published module
`Langlands.Analysis.LocalEllipticCutoffEstimate` (Worker 815), which this file
imports unchanged.

- `derivWordNorm k u x` is
  `√(∑_{w : Fin k → Fin d} ‖iteratedFDeriv ℝ k u x (e ∘ w)‖²)`, where `e` is
  the standard basis of `EuclideanSpace ℝ (Fin d)`. Every ordered word `w` is
  counted once and repeated letters are kept, so this is the Hilbert–Schmidt
  norm of the complete `k`-th derivative tensor in the standard basis. For
  `k = 0` it is `‖u x‖`. The derivative is Mathlib's global `iteratedFDeriv`.
  Because `S` is open, its value at a point of `S` depends only on `u` near that
  point.
- `ballWeightedSeminorm G x₀ R k` is
  `⨆_{ρ ∈ Set.Ico (R / 2) R} ENNReal.ofReal ((R - ρ) ^ k) * eLpNorm G 2 (volume.restrict (Metric.ball x₀ ρ))`,
  a value in `ℝ≥0∞` that may in general be `∞`. The balls are open and
  `ρ < R`, so each of them lies in `Metric.closedBall x₀ R ⊆ S`.

## Scope

- The implication is vacuous when `d = 0` or `r = 0`. In the
  analytic-regularity development those cases are a separate obligation, the
  published statement `ScalarEllipticAnalyticityDegenerateStatement`. This
  statement neither uses nor implies that one.
- Only the canonical Euclidean space and basis are treated here. The step from
  the canonical case to an arbitrary normed space with an actual basis is the
  separate obligation stated by the published
  `EuclideanScalarEllipticAnalyticityTransportStatement`. This statement neither
  uses nor implies that one either.
- The factorial induction that would prove this statement is separate work, as
  are any downstream pointwise (Sobolev) bounds, real analyticity of `u` and
  automorphic applications. None of them is a hypothesis here.

## Provenance

This is a derived scalar specialization of Morrey–Nirenberg, *On the
analyticity of the solutions of linear elliptic systems of partial differential
equations* (Comm. Pure Appl. Math. 1957). It is registered as source
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`.
The relevant material is §5, "General Elliptic Systems", on printed
pp. 287–290 (PDF pp. 17–20).

- (5.3), printed p. 287: `d_p(u, B_ρ)` is the `L²(B_ρ)` norm of the
  derivatives `∇^{s+t_k+p} u_k`, for `p ≥ -(s+t)`.
- (5.4), printed p. 288:
  `N_{R,p}(u) = [p!]^{-1} sup_{R/2 ≤ ρ < R} (R - ρ)^{s+t+p} d_p(u, B_ρ)`.
- (5.5), printed p. 288: `N_{R,p}(u) ≤ M λ^p` for `p ≥ -(s+t)`, for all `R`
  below a constant `R₁`.
- On printed p. 290, (5.5) is derived by induction on `p` from Lemma 5.4. That
  argument rests on the constant-coefficient Lemmas 5.1–5.3 (printed
  pp. 288–289), which include the nested-ball recurrence (5.9).

For a single scalar equation of order `r` we have `s + t = r`. Put
`k = r + p`, so `p ≥ -r` exactly when `k ≥ 0`. Then the quantity inside (5.4)
becomes `(R - ρ)^k ‖∇^k u‖_{L²(B_ρ)}` divided by `[(k - r)!]`, which is
`ballWeightedSeminorm` with weight exponent `k`. With `λ ≥ 1` and
`[(k - r)!] ≤ k!`, (5.5) gives a bound of the form `C A^k k!`. This holds up to
the normalization of `|∇^k u|` relative to `derivWordNorm`, which changes the
constants only by factors of the form `c^k`.

The following are internal and are not a verbatim transcription of the
source:

- the open-set, pointwise-ellipticity hypotheses;
- the quantifier order with an arbitrary upper radius `R₀`, which plays the
  role of the source's small radius `R < R₁`;
- the complete ordered-tensor norm;
- the `ℝ≥0∞`-valued weighted seminorm.

# Cauchy estimates and holomorphic parametric integrals

Module `Langlands.Analysis.SeveralComplex.ParametricHolomorphy`, namespace
`Langlands.Analysis.SeveralComplex`.

Throughout, `E` and `F` are complex normed spaces. The last three results assume that `E` is
finite-dimensional. No completeness of `F` is assumed (for a non-complete `F` Mathlib's
integrals are `0`, and the results hold trivially).

## Results

- `norm_fderiv_le_of_forall_norm_le` (**Cauchy estimate in several variables**). If
  `f : E → F` is complex differentiable on the open ball `ball x r` and `‖f y‖ ≤ M` for all
  `y` in that ball, then for every `0 < r' < r` the operator norm of the complex derivative
  satisfies `‖fderiv ℂ f x‖ ≤ M / r'`.

- `continuous_fderiv_param`. Let `W ⊆ E` be open and `G : E → ℝ → F` such that
  `(z, θ) ↦ G z θ` is continuous on `W × ℝ` and `z ↦ G z θ` is complex differentiable on `W`
  for every `θ`. Then for each `x₀ ∈ W` the map `θ ↦ fderiv ℂ (fun z => G z θ) x₀` is
  continuous.

- `differentiableOn_intervalIntegral_of_continuousOn` (**holomorphic dependence of an interval
  integral on a parameter**). Under the same hypotheses on `G`, for all real `a`, `b` the map
  `z ↦ ∫ θ in a..b, G z θ` is complex differentiable on `W`.

- `differentiableOn_circleIntegral_of_continuousOn` (**holomorphic dependence of a circle
  integral on a parameter**). If `G : E → ℂ → F` is continuous on `W × sphere c |R|` and
  `z ↦ G z t` is complex differentiable on `W` for every `t` on the circle `sphere c |R|`, then
  `z ↦ ∮ t in C(c, R), G z t` is complex differentiable on `W`.

## Proofs

- Cauchy estimate: for a direction `u ≠ 0` put `R = r' / ‖u‖` and restrict `f` to the complex
  line `t ↦ x + t • u`. The restriction `g` is differentiable on a neighbourhood of the closed
  disc of radius `R` about `0` (its image lies in `ball x r` because `R ‖u‖ = r' < r`), and is
  bounded by `M` on the circle of radius `R`. Mathlib's one-variable Cauchy estimate
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` gives `‖g'(0)‖ ≤ M / R`, and by the chain
  rule `g'(0) = Df(x) u`. Hence `‖Df(x) u‖ ≤ (M / r') ‖u‖`, which bounds the operator norm
  (`ContinuousLinearMap.opNorm_le_bound`; `M ≥ 0` because `‖f x‖ ≤ M`).

- Continuity of the derivative in `θ`: choose `r > 0` with `ball x₀ r ⊆ W`. The set
  `closedBall x₀ (r/2) × [θ₀ - 1, θ₀ + 1]` is compact (`E` is finite-dimensional, hence proper),
  so `G` is uniformly continuous on it (Heine–Cantor). For `θ` close to `θ₀` the difference
  `z ↦ G z θ - G z θ₀` is therefore uniformly small on `ball x₀ (r/2)`, and the Cauchy estimate
  with radii `r/2 > r/4` bounds `‖D_z G(x₀, θ) - D_z G(x₀, θ₀)‖`.

- Interval integrals: apply Mathlib's differentiation under the integral sign,
  `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, on the ball
  `ball x₀ (r/4)`, with the derivative `fderiv ℂ (fun z => G z θ) x`. The integrands are
  continuous in `θ`, hence measurable, and the derivative at `x₀` is continuous in `θ` by the
  previous result. A bound `M` for `‖G‖` on the compact set `closedBall x₀ (r/2) × [[a, b]]` and
  the Cauchy estimate on balls `ball x (r/4) ⊆ closedBall x₀ (r/2)` give the constant
  dominating function `M / (r/8)` for the derivatives.

- Circle integrals: unfold `circleIntegral` as the interval integral over `[0, 2π]` of
  `deriv (circleMap c R) θ • G z (circleMap c R θ)` and apply the interval result; the
  integrand is jointly continuous because `circleMap c R` is continuous with values in
  `sphere c |R|` and `deriv (circleMap c R) θ = circleMap 0 R θ * I`.

## Provenance

Internal. These are standard facts of complex analysis (Cauchy's estimates; holomorphy of
integrals depending holomorphically on a parameter), written here as supporting lemmas for the
proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`
(Bernstein–Lapid, Theorem 3.3), where they are used to show that integrals over circles of
holomorphic families stay holomorphic in the remaining variables. The Lean proofs follow the
route described above and use only Mathlib.

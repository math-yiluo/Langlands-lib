# Directional derivatives of holomorphic maps are holomorphic

Module `Langlands.Analysis.SeveralComplex.LineDerivative`, namespace
`Langlands.Analysis.SeveralComplex`.

`E` is a complex normed space and `F` a complex Banach space (`CompleteSpace F`); the last result
assumes that `E` is finite-dimensional.

## Results

- `hasDerivAt_comp_line`: if `h : E → F` is complex differentiable at `z`, then
  `s ↦ h (z + s • v)` has derivative `fderiv ℂ h z v` at `s = 0`. (This one needs no
  completeness of `F`.)
- `fderiv_apply_eq_circleIntegral` (**Cauchy formula for a directional derivative**): if `h` is
  complex differentiable on an open set `U` and `z + s • v ∈ U` for all `‖s‖ ≤ ε` (`ε > 0`), then

  `fderiv ℂ h z v = (2πi)⁻¹ • ∮_{|s| = ε} (1 / s²) • h (z + s • v) ds`.

- `differentiableOn_fderiv_apply`: if `E` is finite-dimensional and `h` is complex
  differentiable on an open set `U`, then for every `v : E` the map `z ↦ fderiv ℂ h z v` is
  complex differentiable on `U`.

## Proofs

- The first item is the chain rule for `s ↦ z + s • v` (derivative `v`) followed by `h`.
- Cauchy formula: `s ↦ h (z + s • v)` is differentiable on the closed disc `|s| ≤ ε`, so
  Mathlib's `DifferentiableOn.deriv_eq_smul_circleIntegral` gives
  `∮ (1/s²) • h(z + s • v) = 2πi • deriv (s ↦ h (z + s • v)) 0`, and the derivative at `0` is
  `fderiv ℂ h z v` by the first item.
- Holomorphy: given `z₀ ∈ U`, choose `r > 0` with `ball z₀ r ⊆ U` and
  `ε = r / (2 (‖v‖ + 1))`, so that `ε ‖v‖ < r/2`. For `z ∈ ball z₀ (r/2)` and `‖s‖ ≤ ε` the point
  `z + s • v` lies in `ball z₀ r`. On `ball z₀ (r/2)` the map `z ↦ fderiv ℂ h z v` therefore
  agrees with `z ↦ (2πi)⁻¹ • ∮_{|s| = ε} (1/s²) • h (z + s • v)`. The integrand is jointly
  continuous on `ball z₀ (r/2) × sphere 0 ε` and holomorphic in `z`, so this integral is
  holomorphic in `z` by `differentiableOn_circleIntegral_of_continuousOn` (module
  `Langlands.Analysis.SeveralComplex.ParametricHolomorphy`). Hence `z ↦ fderiv ℂ h z v` is
  differentiable at `z₀`.

## Provenance

Internal. This is a standard consequence of the Cauchy integral formula (holomorphic maps have
holomorphic derivatives), proved here for directional derivatives on finite-dimensional
spaces because Mathlib has it only for functions of one complex variable. It is a supporting
lemma for the proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`
(Bernstein–Lapid, Theorem 3.3). There it makes the `t`-derivative of a holomorphic function
`H (w, t)` holomorphic in all variables (module `ZeroCounting`).

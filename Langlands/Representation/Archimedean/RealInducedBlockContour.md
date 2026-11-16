# A contour bound for rotation integrals of induced `GL_2(ℝ)` blocks

Lean module: `Langlands.Representation.Archimedean.RealInducedBlockContour`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It is
the analytic input for bounds on the rotation (torus) averages of functions in real standard
modules whose block list contains induced (discrete-series) blocks `D_m`. The module imports only
Mathlib. Unprefixed names below are in the namespace
`Langlands.Archimedean.RealInducedBlockContour`.

## Definitions

* `wave u w θ = u e^{iθ} + w e^{-iθ}` for `u, w ∈ ℂ`, `θ ∈ ℝ`; write `X(θ)` for it.
* `holo u w l n z = (u z² + w)^l / (ū + w̄ z²)^n` for `l, n ∈ ℕ`, `z ∈ ℂ`; write `G(z)` for it.

## Results

* `conj_wave`: `conj(X(θ)) = ū e^{-iθ} + w̄ e^{iθ}`.
* `den_ne_zero`: if `|w| < |u|` and `|z| ≤ 1` then `ū + w̄ z² ≠ 0`.
* `integrand_eq`: for `N ∈ ℤ`,
  `X(θ)^l / conj(X(θ))^n · e^{iNθ} = G(e^{iθ}) · (e^{iθ})^{n − l + N}`.
* `circleIntegral_eq`: for `k ∈ ℤ`, the circle integral `∮_{|z| = 1} G(z) z^{k−1} dz` equals
  `i ∫₀^{2π} G(e^{iθ}) (e^{iθ})^k dθ`.
* `norm_holo_le`: if `|w| < |u|` and `|z| = 1/2` then
  `|G(z)| ≤ ((5/4)|u|)^l / ((3/4)|u|)^n`.
* `norm_integral_le` (**contour bound**): if `|w| < |u|`, then for all `l, n ∈ ℕ` and `N ∈ ℤ`,

  `|∫₀^{2π} X(θ)^l / conj(X(θ))^n · e^{iNθ} dθ| ≤ 2π (1/2)^{n − l + N} ((5/4)|u|)^l / ((3/4)|u|)^n`,

  where the power `(1/2)^{n − l + N}` has an integer exponent.

## Proof

`integrand_eq` substitutes `z = e^{iθ}`, `e^{-iθ} = z⁻¹`, and uses
`u z + w z⁻¹ = (u z² + w) z⁻¹` and `ū z⁻¹ + w̄ z = (ū + w̄ z²) z⁻¹`. `circleIntegral_eq` unfolds
Mathlib's `circleIntegral` (`circleMap 0 1 θ = e^{iθ}`, derivative `i e^{iθ}`).

For `norm_holo_le`, `|z|² = 1/4` gives `|u z² + w| ≤ |u|/4 + |w| ≤ (5/4)|u|` and
`|ū + w̄ z²| ≥ |u| − |w|/4 ≥ (3/4)|u|`.

For `norm_integral_le`, put `k = n − l + N` and `f(z) = G(z) z^{k−1}`. On the closed annulus
`1/2 ≤ |z| ≤ 1` the function `f` is continuous, and it is complex differentiable on the open
annulus: the denominator of `G` does not vanish by `den_ne_zero` and `z ≠ 0`. Mathlib's
`circleIntegral_eq_of_differentiable_on_annulus_off_countable` (with the empty exceptional set)
gives `∮_{|z|=1} f = ∮_{|z|=1/2} f`. On `|z| = 1/2`, `norm_holo_le` gives
`|f(z)| ≤ ((5/4)|u|)^l / ((3/4)|u|)^n · (1/2)^{k−1}`, and
`circleIntegral.norm_integral_le_of_norm_le_const` bounds the integral over the circle of radius
`1/2` by `2π · (1/2)` times this. By `integrand_eq` and `circleIntegral_eq` the left side of the
claim equals `|∮_{|z|=1} f|` (`|i| = 1`), and `(1/2)·(1/2)^{k−1} = (1/2)^k`.

## Use

Write the `K`-type `j` function of `D_m` on the block as `ρ^{-(m+1)} (Z/ρ)^j`, where `Z` is the
last row of the block read as a complex number and `ρ = |Z|`. Along the rotations this function
has the shape `X^l / conj(X)^{l+m+1}` (or its conjugate). The bound then gives decay
`|u|^{-(m+1)}`; see `RealInducedBlockSlice`.

## Provenance

This is derived, internal infrastructure, written for the Langlands-quotient proof of Task 6749.
The estimate is the elementary Cauchy-theorem estimate of a trigonometric integral by moving the
contour from `|z| = 1` to `|z| = 1/2`. The constants `5/4`, `3/4` and `1/2` are this module's
choices. No literature statement is formalized here.

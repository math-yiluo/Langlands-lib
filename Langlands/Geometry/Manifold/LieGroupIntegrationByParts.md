# Integration by parts for invariant derivatives on a Lie group

Module `Langlands.Geometry.Manifold.LieGroupIntegrationByParts` works on a real Lie group `G`
modelled on a normed space `E` (`ChartedSpace E G`, `LieGroup 𝓘(ℝ, E) ∞ G`). The invariant
derivative is the Library's `groupDirectionalValue 𝓘(ℝ, E) X f g`, the derivative of
`h ↦ f(g h)` at `h = 1` in the direction `X` of the Lie algebra.

## Results

- `hasDerivAt_mul_curve`: if `curve` is an integral curve of the left-invariant vector field of
  `X` at `t`, then `r ↦ f(x · curve r)` has derivative `(X f)(x · curve t)` at `t`, for smooth
  `f`. The proof is the chain rule and `groupDirectionalValue_eq_invariant` with
  `groupDirectionalValue_leftTranslation`.
- `exists_groupDirectionalCurve` (complete `E`): there are a curve with `curve 0 = 1`,
  continuous on a closed ball `[-ε, ε]`, and the identity above for every smooth `f`, every `x`
  and `|t| < ε`. The curve is Mathlib's local integral curve
  (`exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`) of the smooth invariant field.
- `groupDirectionalValue_eq_zero_of_notMem_tsupport`, `tsupport_groupDirectionalValue_subset`,
  `HasCompactSupport.groupDirectionalValue`: the derivative vanishes off `tsupport ψ`, because
  `h ↦ ψ(g h)` vanishes near `1`. So derivatives preserve compact support.
- `integral_groupDirectionalValue_mul`: for a right-invariant measure `μ` that is finite on
  compact sets, smooth `f` and smooth compactly supported `ψ`,
  `∫ (X f) ψ dμ = -∫ f (X ψ) dμ`.
- `eq_zero_of_forall_integral_mul_eq_zero` (finite-dimensional `E`, Hausdorff `G`): for a measure
  positive on nonempty open sets and finite on compact sets, a continuous `Θ` with
  `∫ Θ ψ dμ = 0` for all smooth compactly supported `ψ` is zero.

## Proofs

Integration by parts: let `Φ(t) = ∫ f(x c(t)) ψ(x c(t)) dμ(x)` for the curve `c` of
`exists_groupDirectionalCurve`. Right invariance of `μ` (`integral_mul_right_eq_self`) makes `Φ`
constant. Differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
identifies `Φ'(0)` with `∫ ((X f) ψ + f (X ψ)) dμ`. For `|t| < ε` the derivative at `x c(t)`
vanishes unless `x` lies in the compact set `tsupport ψ · c([-ε, ε])⁻¹`. It is bounded there by
its maximum on `tsupport ψ`, so the bound is a constant times the indicator of a compact set.
Uniqueness of derivatives gives `∫ ((X f) ψ + f (X ψ)) dμ = 0`. Both summands are integrable,
since they are continuous with compact support.

Separation: if `Θ(x₀) ≠ 0`, put `a = conj Θ(x₀)`. Then `Re(a Θ) > 0` on a neighbourhood of `x₀`.
Take a smooth bump function `β ≥ 0` at `x₀` with `tsupport β` inside this neighbourhood
(`SmoothBumpFunction.nhds_basis_tsupport`) and `ψ = a β`. The real part of `∫ Θ ψ dμ` is the
integral of the continuous nonnegative function `Re(a Θ) β`, which is positive at `x₀`. It is
therefore positive (`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`), a
contradiction.

## Provenance

These are standard facts of analysis on Lie groups, proved here with Mathlib's manifold calculus.
They are internal tools for the uniform center ideal of intertwining integrals.

# Simple roots of arbitrary polynomials over henselian local rings

Module `Langlands.CommutativeAlgebra.HenselianSimpleRoots`.

Mathlib's `HenselianLocalRing` asks that simple residual roots of *monic* polynomials lift. This
module records the version without monicity, together with two small facts used with it.

- `powerSeries_henselianLocalRing` (instance): the power series ring `k⟦X⟧` over a field is a
  henselian local ring. It is complete for its maximal ideal `(X)` (Mathlib's instance
  `IsAdicComplete (Ideal.span {X}) (PowerSeries k)`), so Mathlib's
  `IsAdicComplete.henselianRing` applies, and `PowerSeries.maximalIdeal_eq_span_X` identifies
  the ideal.
- `exists_isRoot_sub_mem_maximalIdeal`: over a henselian local ring `O`, every polynomial `f`
  (not necessarily monic) with `f(a₀) ∈ 𝔪` and `f'(a₀)` a unit has a root `a` with
  `a - a₀ ∈ 𝔪`.
- `eq_of_isRoot_of_sub_mem_maximalIdeal`: in any local ring two roots of `f` that are congruent
  modulo `𝔪` coincide when `f'` is a unit at one of them (Mathlib's
  `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`, restated with the maximal ideal).

## Proof of the lifting

Write `g(Z) = f(a₀ + Z) = c₀ + u Z + g₂ Z² + ⋯ + gₙ Zⁿ` (Mathlib's `Polynomial.taylor`), so
`c₀ = f(a₀) ∈ 𝔪` and `u = f'(a₀)` is a unit. Substituting `Z = -c₀ u⁻¹ W` gives
`g(-c₀ u⁻¹ W) = c₀ P(W)` with
`P(W) = 1 - W + Σ_{i ≥ 2} gᵢ (-u⁻¹)ⁱ c₀^(i-1) Wⁱ`,
whose coefficients of degree at least two lie in `𝔪`. Such a polynomial has a root `W` over a
henselian local ring by `Langlands.AlgebraicGeometry.PointTopology.HenselianRoot.exists_isRoot_of_coeff`
(its reflection is monic). Then `a = a₀ - c₀ u⁻¹ W` is a root of `f` with `a - a₀ ∈ 𝔪`. The
identity `g(-c₀ u⁻¹ W) = c₀ P(W)` is checked coefficientwise, so no division by `c₀` is needed.

Provenance: standard commutative algebra; simple roots of arbitrary polynomials lift over
henselian local rings is one of the usual equivalent forms of the henselian property (compare
the Stacks Project, Section 10.153, on henselian local rings).

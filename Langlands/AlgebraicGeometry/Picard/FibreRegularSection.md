# Sections not vanishing on integral fibres

Authors: Worker 5705.

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`), written for Task 5705. It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal`.

- `eq_zero_of_ideal_eq_bot`: on an integral scheme, a section whose zero ideal vanishes on a
  nonempty affine open is zero.
- `fibrePoint`, `fibreChart`, `fibreChartι`: for an affine open `U ⊆ f⁻¹V` and a field `K` over
  `Γ(S, V)`, the affine chart `Spec(Γ(X, U) ⊗ K)` of the fibre `X ×_S Spec K`.
- `isDomain_tensor`: if `f` is geometrically integral (Mathlib's `GeometricallyIntegral`), then
  `Γ(X, U) ⊗ K` is a domain (or zero).
- `appLE_fibreChart_eq_zero`, `tmul_ne_zero`: if a section `σ` does not vanish on the fibre over
  `K`, its local equation `s` on `U` satisfies `s ⊗ 1 ≠ 0`.
- `isFrameOn_trivGen` and `isRegularSection_and_isRelativeEffectiveCartierIdeal`: for `f` flat and
  geometrically integral with `X` locally noetherian, a section of a line bundle that does not
  vanish on any fibre `X_K` (all fields `K` and all `Spec K ⟶ S`) is regular, and its zero ideal is
  a relative effective Cartier ideal (`LocalEquationCartier.isRelativeEffectiveCartierIdeal_of_fibreRegular`
  with `FibreLocalDomain.isSMulRegular_of_isDomain_fiber`).

## Source

Kleiman, *The Picard scheme*, p.25, proof of Theorem 3.13: when the geometric fibres are integral,
a section that is nonzero on every fibre defines a relative effective divisor (Lemma 3.4 with
integral fibres).

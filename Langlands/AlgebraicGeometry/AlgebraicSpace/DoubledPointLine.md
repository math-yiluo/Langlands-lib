# Two affine lines glued along a translate of a punctured line

Author: Worker 105.

Helper module for the proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedOfFiniteTypeStatement`.
It contains no statement from the literature. It builds the scheme used as the
counterexample: over the closed unit ball `O` of a normed field `K`, with `0 < ‖p‖ < 1`,
its generic fibre is (informally) the affine line with a doubled point. The module itself
works over any commutative ring `R` and any `p ∈ R`, and proves nothing about generic fibres.

## Construction

Take two copies of the affine line, `Spec R[t]` (chart `true`) and `Spec R[s]` (chart
`false`); both are `Spec R[X]` in Lean. Glue them along the opens `D(p t)` and
`D(p (p s - 1))`, identified by `t = p s - 1`. The gluing uses `CommonOpenGluing` with the
common open `W = Spec B₂`, where `B₂ = R[s][1/(p (p s - 1))]`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.DoubledPointLine`, for `R` and `p`.

- `f₁ = C p * X` (the function `p t`) and `f₂ = C p * (C p * X - 1)` (the function
  `p (p s - 1)`).
- `B₁ = Localization.Away f₁` and `B₂ = Localization.Away f₂`.
- `isUnit_p₁`, `isUnit_t₁`, `isUnit_p₂`: `p` and `t` are units in `B₁`, and `p` is a unit
  in `B₂`, since `f₁` and `f₂` are.
- `α : R[X] →+* B₂`, `t ↦ p s - 1` (`Polynomial.eval₂RingHom`), and `β : R[X] →+* B₁`,
  `s ↦ (1 + t)/p`. The lemmas `α_C`, `β_C`, `α_f₁`, `β_f₂` give their values on constants
  and show `α f₁ = f₂` and `β f₂ = f₁` in the localizations.
- `ψ : B₁ →+* B₂` and `χ : B₂ →+* B₁`, the maps induced by `α` and `β`
  (`IsLocalization.Away.lift`); `χ_ψ` and `ψ_χ` show that they are inverse. The proofs
  check the generators with `IsLocalization.ringHom_ext` and `Polynomial.ringHom_ext`.
  `ringEquiv : B₁ ≃+* B₂` packages them.
- `isLocalization_α`: with the algebra structure given by `α`, `B₂` is a localization of
  `R[t]` away from `f₁` (transport along `ringEquiv`, `IsLocalization.isLocalization_of_algEquiv`).
- `g₁ = Spec.map α` and `g₂ = Spec.map (algebraMap R[X] B₂)` are open immersions
  (`IsOpenImmersion.of_isLocalization`). `g` indexes them by `ULift Bool`
  (`true ↦ g₁`, `false ↦ g₂`).
- `glued` (the glued scheme) and `ι b` (the chart open immersions), from
  `CommonOpenGluing`.
- `α_comp_algebraMap`, `g_comp_structure`: both charts have the same structure morphism
  to `Spec R` on the common open.
- `toBase : glued ⟶ Spec R` (`CommonOpenGluing.desc`) and `ι_toBase`: on each chart it is
  the structure morphism `Spec R[X] ⟶ Spec R`.

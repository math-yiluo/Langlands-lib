# Descent of smoothness to finitely generated subalgebras (proof)

Proof for task `8836e68b-90ba-4f01-a129-026ad9adfa9d`.

## Statement proved

`Langlands.AlgebraicGeometry.NoetherianApproximation.smoothSubalgebraDescent :
SmoothSubalgebraDescentStatement.{u}`, for an arbitrary universe `u`. The statement is the published
proposition of module `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements`
(statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`): for commutative rings `A₀ → A` in
`Type u`, a quasi-compact morphism `f : X ⟶ Spec A₀` that is locally of finite presentation and whose
base change `pullback.snd f (Spec.map (algebraMap A₀ A))` is smooth, and a finite set `s ⊆ A`, there is
a finitely generated `A₀`-subalgebra `T ⊇ s` of `A` such that the base change
`pullback.snd f (Spec.map (algebraMap A₀ ↥T))` is smooth.
Source: Stacks Project Lemma 32.8.9 (tag 0C0C, smoothness descends along limits), applied to the
presentation of `A` as the directed union of its finitely generated `A₀`-subalgebras.

## Proof

The proposition body is word for word the statement of the ported FLT theorem
`AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd` (module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd`).
The proof binds the morphism `f`, its three instance hypotheses (quasi-compact, locally of finite
presentation, smooth base change) and the finite set `s` (the rings and algebra instances are implicit
binders) and applies that theorem.

The FLT proof, in the imported port modules, runs as follows (see their Markdown files): in the affine
case, Mathlib's `Algebra.Smooth.exists_subalgebra_fg` gives a smooth model `B₁` over a finitely
generated subalgebra `A₁` with `A ⊗[A₁] B₁ ≅ A ⊗[A₀] B₀`; that isomorphism of finitely presented
algebras descends to a finitely generated `T ⊇ A₁ ∪ s` by the direct-limit theorem
`Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit`, so
`T ⊗[A₀] B₀` is smooth over `T`. The global case takes a finite affine open cover of the
quasi-compact `X`, applies the affine case to each chart, collects all generators in one `T`
(smoothness persists over larger subalgebras), and concludes because smoothness is local on the
source.

## Dependencies

- `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements` (Library).
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd`
  and its import closure: 7 further ported FLT modules of the same contribution and
  `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit` (Library, ported by task
  `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`). Apache License 2.0, Copyright 2026 Anthropic, PBC, see
  `licenses/Anthropic-FLT/`.

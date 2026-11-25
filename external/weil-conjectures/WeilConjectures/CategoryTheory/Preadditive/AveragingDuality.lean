/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Duality restricted to averaging summands

Let `Γ` be a finite group whose order `n` is invertible on `T₁`. Let `u₁ : A ⟶ T₁` and
`u₂ : B ⟶ T₂` be split monomorphisms, with retractions `r₁` and `r₂`, onto the images of the
averaging idempotents of actions `ρ₁`, `ρ₂` of `Γ`, that is `n • (r ≫ u) = ∑ a, ρ a`. Let `𝔻` be a
contravariant additive functor and `f : T₁ ⟶ 𝔻 T₂` an isomorphism which intertwines `ρ₁` with the
contragredient action `a ↦ 𝔻(ρ₂ a⁻¹)`. Then the restriction

```
A ──u₁──▶ T₁ ──f──▶ 𝔻 T₂ ──𝔻(u₂)──▶ 𝔻 B
```

of `f` to the two invariant summands is an isomorphism, with inverse `𝔻(r₂) ≫ f⁻¹ ≫ r₁`
(`CategoryTheory.isIso_comp_comp_map_op_of_averaging`).

This is the last step of the proof of blueprint `lemma-nearby-duality-slice--1`: the restriction of
the duality map of nearby cycles to the special fibre of a generic slice is the restriction of the
duality map of the slice to the summands of invariants under the pro-`p` kernel `P`, and the
latter is an isomorphism (blueprint `lemma-duality-invariants-pro-p--1`). By the stabilization of
the `P`-action at a finite level, the summands are the images of averaging idempotents of finite
`p`-group quotients of `P` (`CategoryTheory.nsmul_normalizedTrace_comp_eq_sum`), as here.

-/

@[expose] public section

open CategoryTheory Category Opposite

namespace CategoryTheory

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
  (𝔻 : Cᵒᵖ ⥤ D) [𝔻.Additive] {Γ : Type*} [Group Γ] [Fintype Γ]

/-- An isomorphism `f : T₁ ⟶ 𝔻 T₂` intertwining `ρ₁` with the contragredient of `ρ₂` conjugates
the dual of the averaging idempotent `e₂ = r₂ ≫ u₂` into the averaging idempotent `r₁ ≫ u₁`. -/
lemma comp_map_op_comp_inv_eq_of_averaging {A T₁ : D} {B T₂ : C} {u₁ : A ⟶ T₁} {r₁ : T₁ ⟶ A}
    {ρ₁ : Γ → (T₁ ⟶ T₁)} (hρ₁ : Fintype.card Γ • (r₁ ≫ u₁) = ∑ a, ρ₁ a) {u₂ : B ⟶ T₂}
    {r₂ : T₂ ⟶ B} {ρ₂ : Γ → (T₂ ⟶ T₂)} (hρ₂ : Fintype.card Γ • (r₂ ≫ u₂) = ∑ a, ρ₂ a)
    (f : T₁ ⟶ 𝔻.obj (op T₂)) [IsIso f] (hf : ∀ a, ρ₁ a ≫ f = f ≫ 𝔻.map (ρ₂ a⁻¹).op)
    [IsIso (Fintype.card Γ • 𝟙 T₁)] :
    f ≫ 𝔻.map (r₂ ≫ u₂).op ≫ inv f = r₁ ≫ u₁ := by
  rw [← cancel_epi (Fintype.card Γ • 𝟙 T₁), Preadditive.nsmul_comp, Preadditive.nsmul_comp,
    id_comp, id_comp, ← Preadditive.comp_nsmul, ← Preadditive.nsmul_comp, ← 𝔻.map_nsmul,
    ← show (Fintype.card Γ • (r₂ ≫ u₂)).op = Fintype.card Γ • (r₂ ≫ u₂).op from rfl, hρ₂,
    hρ₁, op_sum, 𝔻.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Fintype.sum_equiv (Equiv.inv Γ) _ _ fun a ↦ ?_
  rw [Equiv.inv_apply, ← assoc, IsIso.comp_inv_eq, hf, inv_inv]

/-- **Duality restricted to averaging summands** (blueprint `lemma-nearby-duality-slice--1`,
"Conclusion", with `lemma-duality-invariants-pro-p--1`): if `u₁`, `u₂` are split by `r₁`, `r₂` with
averaging idempotents `n • (r ≫ u) = ∑ a, ρ a` (`n = |Γ|` invertible on `T₁`) and the isomorphism
`f : T₁ ⟶ 𝔻 T₂` intertwines `ρ₁` with the contragredient action `a ↦ 𝔻(ρ₂ a⁻¹)`, then
`u₁ ≫ f ≫ 𝔻(u₂) : A ⟶ 𝔻 B` is an isomorphism. -/
theorem isIso_comp_comp_map_op_of_averaging {A T₁ : D} {B T₂ : C} {u₁ : A ⟶ T₁}
    {r₁ : T₁ ⟶ A} (h₁ : u₁ ≫ r₁ = 𝟙 A) {ρ₁ : Γ → (T₁ ⟶ T₁)}
    (hρ₁ : Fintype.card Γ • (r₁ ≫ u₁) = ∑ a, ρ₁ a) {u₂ : B ⟶ T₂} {r₂ : T₂ ⟶ B}
    (h₂ : u₂ ≫ r₂ = 𝟙 B) {ρ₂ : Γ → (T₂ ⟶ T₂)} (hρ₂ : Fintype.card Γ • (r₂ ≫ u₂) = ∑ a, ρ₂ a)
    (f : T₁ ⟶ 𝔻.obj (op T₂)) [IsIso f] (hf : ∀ a, ρ₁ a ≫ f = f ≫ 𝔻.map (ρ₂ a⁻¹).op)
    [IsIso (Fintype.card Γ • 𝟙 T₁)] :
    IsIso (u₁ ≫ f ≫ 𝔻.map u₂.op) := by
  have he := comp_map_op_comp_inv_eq_of_averaging 𝔻 hρ₁ hρ₂ f hf
  refine ⟨𝔻.map r₂.op ≫ inv f ≫ r₁, ?_, ?_⟩
  · have : f ≫ 𝔻.map u₂.op ≫ 𝔻.map r₂.op ≫ inv f = r₁ ≫ u₁ := by
      rw [← he, ← 𝔻.map_comp_assoc, ← op_comp]
    rw [assoc, assoc, reassoc_of% this, reassoc_of% h₁, h₁]
  · have : inv f ≫ r₁ ≫ u₁ ≫ f = 𝔻.map (r₂ ≫ u₂).op := by
      rw [← reassoc_of% he, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, comp_id]
    rw [assoc, assoc, reassoc_of% this, ← 𝔻.map_comp, ← 𝔻.map_comp, ← op_comp, ← op_comp,
      reassoc_of% h₂, h₂, op_id, 𝔻.map_id]

end CategoryTheory

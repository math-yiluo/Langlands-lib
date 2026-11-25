/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Endomorphisms of the image of an adjoint

Let `adj : F ⊣ G`. An endomorphism `t` of `G d` is an isomorphism as soon as `F t` is one
(`CategoryTheory.Adjunction.isIso_of_isIso_map_leftAdjoint`): through the adjunction,
precomposition with `t` on `End(G d)` is precomposition with `F t` on `Hom(F G d, d)`, hence
bijective, so `t` has a right inverse `x`, and `t ≫ x ≫ t = t` gives `x ≫ t = 𝟙`. Dually, an
endomorphism `t` of `F c` is an isomorphism as soon as `G t` is one
(`CategoryTheory.Adjunction.isIso_of_isIso_map_rightAdjoint`).

For a proper morphism `a : X ⟶ Spec k`, `F = Ra_*` and `G = Ra^!`, this says that an endomorphism
of the dualizing complex `ω_X = Ra^! ℚ̄_ℓ` is invertible if it is so on global sections.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj in
/-- An endomorphism `t` of `G d`, for an adjunction `F ⊣ G`, is an isomorphism as soon as `F t`
is one. -/
lemma isIso_of_isIso_map_leftAdjoint {d : D} (t : G.obj d ⟶ G.obj d) [IsIso (F.map t)] :
    IsIso t := by
  have key : ∀ y : G.obj d ⟶ G.obj d,
      (adj.homEquiv _ _).symm (t ≫ y) = F.map t ≫ (adj.homEquiv _ _).symm y := fun y ↦ by
    simp [homEquiv_counit]
  have inj : ∀ y₁ y₂ : G.obj d ⟶ G.obj d, t ≫ y₁ = t ≫ y₂ → y₁ = y₂ := fun y₁ y₂ h ↦ by
    apply (adj.homEquiv _ _).symm.injective
    have h' := congrArg (adj.homEquiv _ _).symm h
    rw [key, key] at h'
    exact (cancel_epi _).1 h'
  let x : G.obj d ⟶ G.obj d := adj.homEquiv _ _ (inv (F.map t) ≫ adj.counit.app d)
  have hx : t ≫ x = 𝟙 _ := by
    apply (adj.homEquiv _ _).symm.injective
    rw [key, Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc, homEquiv_counit, F.map_id,
      Category.id_comp]
  exact ⟨x, hx, inj _ _ (by rw [reassoc_of% hx, Category.comp_id])⟩

include adj in
/-- An endomorphism `t` of `F c`, for an adjunction `F ⊣ G`, is an isomorphism as soon as `G t`
is one. -/
lemma isIso_of_isIso_map_rightAdjoint {c : C} (t : F.obj c ⟶ F.obj c) [IsIso (G.map t)] :
    IsIso t := by
  have key : ∀ y : F.obj c ⟶ F.obj c,
      adj.homEquiv _ _ (y ≫ t) = adj.homEquiv _ _ y ≫ G.map t := fun y ↦ by
    simp [homEquiv_unit]
  have inj : ∀ y₁ y₂ : F.obj c ⟶ F.obj c, y₁ ≫ t = y₂ ≫ t → y₁ = y₂ := fun y₁ y₂ h ↦ by
    apply (adj.homEquiv _ _).injective
    have h' := congrArg (adj.homEquiv _ _) h
    rw [key, key] at h'
    exact (cancel_mono _).1 h'
  let x : F.obj c ⟶ F.obj c := (adj.homEquiv _ _).symm (adj.unit.app c ≫ inv (G.map t))
  have hx : x ≫ t = 𝟙 _ := by
    apply (adj.homEquiv _ _).injective
    rw [key, Equiv.apply_symm_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      homEquiv_unit, G.map_id]
    exact (Category.comp_id _).symm
  exact ⟨x, inj _ _ (by rw [Category.assoc, hx, Category.id_comp, Category.comp_id]), hx⟩


end CategoryTheory.Adjunction

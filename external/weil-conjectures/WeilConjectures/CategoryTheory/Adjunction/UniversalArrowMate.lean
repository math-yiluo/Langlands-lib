/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Left adjoints commuting with a functor preserve universal arrows to it

Let `adj₁ : f₁ ⊣ g₁` and `adj₂ : f₂ ⊣ g₂` be adjunctions, with `f₁ : C₁ ⥤ D₁` and
`f₂ : C₂ ⥤ D₂`, and let `u : C₁ ⥤ C₂` and `v : D₁ ⥤ D₂` be functors (restrictions of scalars,
say), with comparisons `β : u ⋙ f₂ ⟶ f₁ ⋙ v` of the left adjoints and `τ : g₁ ⋙ u ⟶ v ⋙ g₂`
of the right adjoints, compatible with the units. If `η : K ⟶ u K'` is a universal arrow from
`K` to `u`, then so is `f₂ η ≫ β : f₂ K ⟶ v (f₁ K')`, from `f₂ K` to `v`, as soon as `τ` is an
isomorphism (`CategoryTheory.Adjunction.bijective_comp_map_of_unit_comp_map`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁] [Category* C₂] [Category* D₂]
  {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} (adj₁ : f₁ ⊣ g₁) {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
  (adj₂ : f₂ ⊣ g₂) {u : C₁ ⥤ C₂} {v : D₁ ⥤ D₂}

/-- **Left adjoints commuting with a functor preserve universal arrows to it.** Let
`β : u ⋙ f₂ ⟶ f₁ ⋙ v` and `τ : g₁ ⋙ u ⟶ v ⋙ g₂` be compatible with the units of
`adj₁ : f₁ ⊣ g₁` and `adj₂ : f₂ ⊣ g₂` (that is, `τ` is the mate of `β`). If every morphism
`K ⟶ u N` factors uniquely through `η : K ⟶ u K'`, and `τ` is invertible at `N'`, then every
morphism `f₂ K ⟶ v N'` factors uniquely through `f₂ η ≫ β : f₂ K ⟶ v (f₁ K')`. -/
lemma bijective_comp_map_of_unit_comp_map (β : u ⋙ f₂ ⟶ f₁ ⋙ v) (τ : g₁ ⋙ u ⟶ v ⋙ g₂)
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.app K) =
      u.map (adj₁.unit.app K) ≫ τ.app (f₁.obj K))
    {K : C₂} {K' : C₁} (η : K ⟶ u.obj K')
    (hη : ∀ N, Function.Bijective fun g : K' ⟶ N ↦ η ≫ u.map g) (N' : D₁)
    [IsIso (τ.app N')] :
    Function.Bijective fun g : f₁.obj K' ⟶ N' ↦ (f₂.map η ≫ β.app K') ≫ v.map g := by
  have h : (fun g : f₁.obj K' ⟶ N' ↦ (f₂.map η ≫ β.app K') ≫ v.map g) =
      (adj₂.homEquiv K (v.obj N')).symm ∘ (fun h ↦ h ≫ τ.app N') ∘
        (fun g : K' ⟶ g₁.obj N' ↦ η ≫ u.map g) ∘ adj₁.homEquiv K' N' := by
    ext g
    simp only [Function.comp_apply, Equiv.eq_symm_apply, homEquiv_unit, Functor.map_comp,
      Category.assoc]
    have h₁ := adj₂.unit.naturality_assoc η (g₂.map (β.app K') ≫ g₂.map (v.map g))
    have h₂ := τ.naturality g
    simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at h₁ h₂
    rw [← h₁, reassoc_of% (hβ K'), ← h₂]
  rw [h]
  exact (adj₂.homEquiv K (v.obj N')).symm.bijective.comp
    (((asIso (τ.app N')).homToEquiv (Z := K)).bijective.comp ((hη _).comp
      (adj₁.homEquiv K' N').bijective))

end CategoryTheory.Adjunction

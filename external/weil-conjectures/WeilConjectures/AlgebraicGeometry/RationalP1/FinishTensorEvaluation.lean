/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Category
/-! # Appending tensor unit comparisons to a prefix evaluation -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.ProEtale.RationalP1
/-- Append a tensor-unit comparison to an evaluated prefix. -/
theorem finish_tensor_evaluation
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    (R : C ⥤ D) (M V U : C) {A : D} {Z U₀ U₁ U₂ : C}
    (a : R.obj M ⟶ A) (b : A ⟶ R.obj Z) (p : Z ⟶ M ⊗ V)
    (f : V ⟶ U) (k₀ : 𝟙_ C ⟶ U₀) (k₁ : U₀ ⟶ U₁)
    (k₂ : U₁ ⟶ U₂) (k₃ : U₂ ⟶ U) (e : U ≅ 𝟙_ C)
    (h : a ≫ b ≫ R.map p ≫ R.map (M ◁ f) =
      R.map (ρ_ M).inv ≫ R.map (M ◁ (k₀ ≫ k₁ ≫ k₂ ≫ k₃))) :
    a ≫ b ≫ R.map (p ≫ (M ◁ f) ≫ (M ◁ e.hom) ≫ (ρ_ M).hom) =
      R.map ((ρ_ M).inv ≫ (M ◁ (k₀ ≫ k₁ ≫ k₂ ≫ k₃ ≫ e.hom)) ≫ (ρ_ M).hom) := by
  have h' := congrArg (fun z ↦ z ≫ R.map (M ◁ e.hom) ≫ R.map (ρ_ M).hom) h
  simpa only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc] using h'

end AlgebraicGeometry.ProEtale.RationalP1

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Transposes of adjunction mates

Source: Stacks 0FND.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a av b bv c cv d dv
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {G : A ⥤ C} {H : B ⥤ D}

/-- The mate is precisely the map intertwining the two adjunction transposes.
Source: Stacks 0FND (auxiliary; not a blueprint node).
Proof: expand both Hom transposes using the units. The unit-mate identity identifies
the initial two factors; naturality of the right square moves f past it. Functoriality
then combines the remaining unit and restricted f into the other Hom transpose. -/
theorem adjunctionMate_transpose (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (τ : TwoSquare R₁ H G R₂) (P : A) (M : B) (f : L₁.obj P ⟶ M) :
    a₂.homEquiv (G.obj P) (H.obj M)
      (((mateEquiv a₁ a₂).symm τ).app P ≫ H.map f) =
    G.map (a₁.homEquiv P M f) ≫ τ.app M := by
  rw [Adjunction.homEquiv_unit, R₂.map_comp, ← Category.assoc]
  erw [← unit_mateEquiv_symm a₁ a₂ τ P, Category.assoc]
  change G.map (a₁.unit.app P) ≫ (τ.app (L₁.obj P) ≫ (H ⋙ R₂).map f) = _
  rw [← τ.naturality f, ← Category.assoc, Functor.comp_map, ← G.map_comp,
    Adjunction.homEquiv_unit]

end CategoryTheory

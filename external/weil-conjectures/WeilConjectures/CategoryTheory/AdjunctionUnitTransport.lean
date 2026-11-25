/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Basic
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Transport of a unit with a prescribed counit -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.Adjunction
/-- A unit component with its source and target objects normalized. -/
def unitComponent {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (M : C) :
    M ⟶ G.obj (F.obj M) := η.app M

/-- The normalized component is the original component. -/
theorem unitComponent_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (M : C) :
    unitComponent F G η M = η.app M := rfl

/-- A componentwise counit equation transports the first triangle.
Source: blueprint thm-amb-p1-adjunction.proof.md, counit comparison.
(auxiliary; not a blueprint node).
Proof: substitute the component equation in the composite and apply the assumed triangle. -/
theorem first_triangle_of_evaluation_eq
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    (e : ∀ K : D, F.obj (G.obj K) ⟶ K)
    (he : ∀ K, ε.app K = e K)
    (h : ∀ M, F.map (unitComponent F G η M) ≫ e (F.obj M) = 𝟙 _) :
    ∀ M, F.map (unitComponent F G η M) ≫ ε.app (F.obj M) = 𝟙 _ := by
  intro M
  rw [he]
  exact h M

/-- A natural right-adjoint comparison transports both triangles with their fixed counit. -/
theorem transport_unit_triangles
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G H : D ⥤ C) (e : G ≅ H)
    (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D) (ε' : H ⋙ F ⟶ 𝟭 D)
    (hε : Functor.whiskerRight e.hom F ≫ ε' = ε)
    (h₁ : ∀ X, F.map (unitComponent F G η X) ≫ ε.app (F.obj X) = 𝟙 _)
    (h₂ : ∀ Y, unitComponent F G η (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 _) :
    ∃ η' : 𝟭 C ⟶ F ⋙ H,
      (∀ X, F.map (η'.app X) ≫ ε'.app (F.obj X) = 𝟙 _) ∧
      (∀ Y, η'.app (H.obj Y) ≫ H.map (ε'.app Y) = 𝟙 _) := by
  let a : F ⊣ G := Adjunction.mkOfUnitCounit
    { unit := η
      counit := ε
      left_triangle := by ext X; simpa [unitComponent] using h₁ X
      right_triangle := by ext Y; simpa [unitComponent] using h₂ Y }
  let a' := a.ofNatIsoRight e
  have heq : a'.counit = ε' := by
    ext Y
    have hh := NatTrans.congr_app hε Y
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hh
    change F.map (e.inv.app Y) ≫ ε.app Y = ε'.app Y
    rw [← hh, ← Category.assoc, ← F.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Category.id_comp]
  refine ⟨a'.unit, ?_, ?_⟩
  · intro X
    rw [← heq]
    exact a'.left_triangle_components X
  · intro Y
    rw [← heq]
    exact a'.right_triangle_components Y
end CategoryTheory.Adjunction

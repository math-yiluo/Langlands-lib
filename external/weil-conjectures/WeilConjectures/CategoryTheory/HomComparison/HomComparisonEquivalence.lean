/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Hom-comparison algebra for abstract functors and equivalences

Source: equivalence unit/counit identities and Stacks 03EO.
(blueprint: lem-sf-hom-comparison-equivalence)
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory Opposite
namespace CategoryTheory.HomComparison

/-- Reverse a two-variable Hom comparison along an equivalence.
Source: Stacks 03EO (blueprint: lem-sf-hom-comparison-equivalence).
Whisker by the inverse in both variables, use the counit to cancel the forward
functor, and then use the unit in the value category. -/
def inverseHomComparison {A B : Type*} [Category A] [Category B] (E : B ≌ A)
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (h : HB ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ HA) :
    HA ⋙ E.inverse ≅ E.inverse.op.prod E.inverse ⋙ HB := by
  let e : (E.inverse.op.prod E.inverse) ⋙ (E.functor.op.prod E.functor) ≅
      𝟭 (Aᵒᵖ × A) := NatIso.prod (NatIso.op E.counitIso.symm) E.counitIso
  exact (Functor.leftUnitor (HA ⋙ E.inverse)).symm ≪≫
    Functor.isoWhiskerRight e.symm (HA ⋙ E.inverse) ≪≫
    Functor.isoWhiskerLeft (E.inverse.op.prod E.inverse)
      (Functor.isoWhiskerRight h.symm E.inverse) ≪≫
    Functor.isoWhiskerLeft ((E.inverse.op.prod E.inverse) ⋙ HB) E.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- Compose two componentwise naturality squares after applying a functor.
Source: Stacks 03EO and functoriality
(blueprint: lem-sf-hom-comparison-equivalence). -/
theorem mapIso_comp_naturality {B D : Type*} [Category B] [Category D] (F : B ⥤ D)
    {X X' Y Y' : B} {Z Z' : D} (e : X ≅ Y) (e' : X' ≅ Y')
    (i : F.obj Y ≅ Z) (i' : F.obj Y' ≅ Z')
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z')
    (he : f ≫ e'.hom = e.hom ≫ g) (hi : F.map g ≫ i'.hom = i.hom ≫ h) :
    F.map f ≫ (F.mapIso e' ≪≫ i').hom = (F.mapIso e ≪≫ i).hom ≫ h := by
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← F.map_comp, he, F.map_comp, Category.assoc, hi, Category.assoc]

end CategoryTheory.HomComparison

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Unit normalization of the clopen adjunction word

Source: Stacks Project, Modules on Sites, Tag 03DI; categorical adjunction calculation.
(blueprint: lem-cbc-clopen-adjunction-unit-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory

namespace CategoryTheory

private theorem openUnitTranspose {A X : Type*} [Category A] [Category X]
    {J : A ⥤ X} {P : X ⥤ A} {D : A ⥤ X}
    (a : J ⊣ P) (b : P ⊣ D) [IsIso a.unit] (N : A) :
    a.unit.app N ≫ (b.homEquiv _ _).symm
      (b.unit.app (J.obj N) ≫ D.map ((inv a.unit).app N)) = 𝟙 N := by
  rw [← b.homEquiv_unit, Equiv.symm_apply_apply, NatIso.isIso_inv_app]
  exact IsIso.hom_inv_id _

private def clopenUnitWord {A X : Type*} [Category A] [Category X]
    {L : A ⥤ X} {G : X ⥤ A} {D : A ⥤ X}
    (a : L ⊣ G) (b : G ⊣ D) [IsIso a.unit] : L ⟶ D :=
  (Functor.rightUnitor L).inv ≫ Functor.whiskerLeft L b.unit ≫
    (Functor.associator L G D).inv ≫ Functor.whiskerRight (inv a.unit) D ≫
      (Functor.leftUnitor D).hom

/-- The canonical word from the leftmost to the rightmost functor of a triple adjunction
has transpose inverse to the first unit, when that unit is invertible.

On each object, the unitors and associator are identities. The word therefore evaluates
as the second unit followed by the rightmost functor applied to the inverse first unit.
The adjunction bijection sends the latter inverse to exactly this composite. Applying
its inverse cancels the bijection, and the first unit cancels its inverse.

Source: Stacks Project, Modules on Sites, Tag 03DI; categorical unit calculation.
(blueprint: lem-cbc-clopen-adjunction-unit-normalization). -/
theorem clopenAdjunctionUnitNormalization {A X : Type*} [Category A] [Category X]
    {L : A ⥤ X} {G : X ⥤ A} {D : A ⥤ X}
    (a : L ⊣ G) (b : G ⊣ D) [IsIso a.unit] (M : A) :
    a.unit.app M ≫ (b.homEquiv _ _).symm
      (((Functor.rightUnitor L).inv ≫ Functor.whiskerLeft L b.unit ≫
        (Functor.associator L G D).inv ≫ Functor.whiskerRight (inv a.unit) D ≫
          (Functor.leftUnitor D).hom).app M) = 𝟙 M := by
  change a.unit.app M ≫ (b.homEquiv _ _).symm ((clopenUnitWord a b).app M) = 𝟙 M
  have ht : (clopenUnitWord a b).app M =
      b.unit.app (L.obj M) ≫ D.map ((inv a.unit).app M) := by
    simp only [clopenUnitWord, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Category.id_comp]
    erw [Category.comp_id]
  rw [ht]
  exact openUnitTranspose a b M


end CategoryTheory

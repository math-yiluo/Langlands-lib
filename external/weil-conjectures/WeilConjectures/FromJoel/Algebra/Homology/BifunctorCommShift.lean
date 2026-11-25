/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Shift.Quotient

/-!
# Compatibilities of bifunctors acting on cochain complexes and shifts

Migrated from `Mathlib/Algebra/Homology/BifunctorCommShift.lean`
on the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Quotient

/- The following declarations are adapted from the end of
`Mathlib/CategoryTheory/Shift/Quotient.lean` on the branch `jriou_localization`
of Joël Riou's mathlib fork (leanprover-community/mathlib4#25848): this final
block of that file is not yet in the pinned mathlib `v4.33.1`. -/

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {r : HomRel C} (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]
  [r.IsCompatibleWithShift A]

lemma commShiftOfFac_aux {F : Quotient r ⥤ D} {G : C ⥤ D}
    (e : functor r ⋙ F ≅ G) (x y : C) (f₁ f₂ : x ⟶ y)
    (h : r f₁ f₂) : G.map f₁ = G.map f₂ := by
  simp only [← NatIso.naturality_1 e]
  dsimp
  rw [Quotient.sound r h]

@[implicit_reducible]
noncomputable def commShiftOfFac {F : Quotient r ⥤ D} {G : C ⥤ D}
    (e : functor r ⋙ F ≅ G) [G.CommShift A] : F.CommShift A :=
  letI := liftCommShift G r A (commShiftOfFac_aux e)
  Functor.CommShift.ofIso (Quotient.natIsoLift _
    (lift.isLift r G (commShiftOfFac_aux e) ≪≫ e.symm)) A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma natTransCommshift_of_fac {F : Quotient r ⥤ D} {G : C ⥤ D}
    (e : functor r ⋙ F ≅ G) [G.CommShift A] :
    letI := commShiftOfFac A e
    NatTrans.CommShift e.hom A := by
  let _ : F.CommShift A := commShiftOfFac A e
  let iso := lift.isLift r G (commShiftOfFac_aux e)
  let iso' := Quotient.natIsoLift _ (iso ≪≫ e.symm)
  have he (X : C) : e.hom.app X = iso'.inv.app ((functor r).obj X) :=
    (Category.comp_id _).symm
  have := Functor.CommShift.ofIso_compatibility iso' A
  constructor
  intro a
  ext X
  have h₁ := NatTrans.shift_app iso'.inv a ((functor r).obj X)
  have h₂ := NatTrans.shift_app_comm iso.inv a X
  dsimp [iso] at h₁ h₂ ⊢
  simpa [Functor.commShiftIso_comp_hom_app, he, h₁] using h₂.symm

end CategoryTheory.Quotient

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CochainComplex

section

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

lemma map₂CochainComplex_obj_commShiftIso_hom_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (y : ℤ) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso y).hom.app K₂ =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom := rfl

lemma map₂CochainComplex_obj_commShiftIso_inv_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (y : ℤ) :
    ((F.map₂CochainComplex.obj K₁).commShiftIso y).inv.app K₂ =
      (mapBifunctorShift₂Iso K₁ K₂ F y).inv := rfl


lemma map₂CochainComplex_flip_obj_commShiftIso_hom_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (x : ℤ) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso x).hom.app K₁ =
      (mapBifunctorShift₁Iso K₁ K₂ F x).hom := rfl

lemma map₂CochainComplex_flip_obj_commShiftIso_inv_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (x : ℤ) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso x).inv.app K₁ =
      (mapBifunctorShift₁Iso K₁ K₂ F x).inv := rfl


end

end CochainComplex

namespace HomotopyCategory

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ F]

noncomputable instance (K₁ : HomotopyCategory C₁ (.up ℤ)) :
    ((F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).obj K₁).CommShift ℤ :=
  Quotient.commShiftOfFac ℤ (F.quotientCompBifunctorMapHomotopyObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) K₁.as)

instance (K₁ : CochainComplex C₁ ℤ) :
    NatTrans.CommShift (F.quotientCompBifunctorMapHomotopyObjIso
      (.up ℤ) (.up ℤ) (.up ℤ) K₁).hom ℤ := by
  apply Quotient.natTransCommshift_of_fac

noncomputable instance (K₂ : HomotopyCategory C₂ (.up ℤ)) :
    ((F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K₂).CommShift ℤ :=
  Quotient.commShiftOfFac ℤ (F.quotientCompBifunctorMapHomotopyFlipObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) K₂.as)

instance (K₂ : CochainComplex C₂ ℤ) :
    NatTrans.CommShift (F.quotientCompBifunctorMapHomotopyFlipObjIso
      (.up ℤ) (.up ℤ) (.up ℤ) K₂).hom ℤ := by
  apply Quotient.natTransCommshift_of_fac

end HomotopyCategory

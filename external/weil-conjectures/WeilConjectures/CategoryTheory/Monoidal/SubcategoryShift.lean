/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# The tensor product of a full monoidal subcategory commutes with the shifts

Let `P` be a full monoidal subcategory of a monoidal category `C` with a shift, stable under the
shift. If `K ⊗ -` (resp. `- ⊗ K`) commutes with the shifts on `C`, so does `K ⊗ -` (resp.
`- ⊗ K`) on `P` (`ObjectProperty.commShiftTensorLeft`, `ObjectProperty.commShiftTensorRight`):
it is the functor induced by the ambient one (`ObjectProperty.tensorLeftIsoLift`), and its
commutation isomorphisms are those of `C` (`ObjectProperty.ι_map_commShiftIso_tensorLeft_hom_app`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]
  {A : Type*} [AddMonoid A] [HasShift C A] [P.IsStableUnderShift A]

/-- The functor `K ⊗ -` on `P` is the functor induced by `K ⊗ -` on `C`. -/
def tensorLeftIsoLift (K : P.FullSubcategory) :
    P.liftFullSubcategory P ((curriedTensor C).obj K.obj) (fun _ hX ↦ P.prop_tensor K.2 hX) ≅
      (curriedTensor P.FullSubcategory).obj K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    ext
    simp)

/-- The functor `- ⊗ K` on `P` is the functor induced by `- ⊗ K` on `C`. -/
def tensorRightIsoLift (K : P.FullSubcategory) :
    P.liftFullSubcategory P ((curriedTensor C).flip.obj K.obj) (fun _ hX ↦ P.prop_tensor hX K.2) ≅
      (curriedTensor P.FullSubcategory).flip.obj K :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    ext
    simp)

/-- The functor `K ⊗ -` on `P` commutes with the shifts. -/
noncomputable instance commShiftTensorLeft (K : P.FullSubcategory)
    [((curriedTensor C).obj K.obj).CommShift A] :
    ((curriedTensor P.FullSubcategory).obj K).CommShift A :=
  Functor.CommShift.ofIso (P.tensorLeftIsoLift K) A

/-- The functor `- ⊗ K` on `P` commutes with the shifts. -/
noncomputable instance commShiftTensorRight (K : P.FullSubcategory)
    [((curriedTensor C).flip.obj K.obj).CommShift A] :
    ((curriedTensor P.FullSubcategory).flip.obj K).CommShift A :=
  Functor.CommShift.ofIso (P.tensorRightIsoLift K) A

/-- The functor `K ⊗ -` on `P` is compatible with `K ⊗ -` on `C` through the inclusion. -/
def tensorLeftCompιIso (K : P.FullSubcategory) :
    (curriedTensor P.FullSubcategory).obj K ⋙ P.ι ≅ P.ι ⋙ (curriedTensor C).obj K.obj :=
  Functor.isoWhiskerRight (P.tensorLeftIsoLift K).symm P.ι ≪≫
    P.liftFullSubcategoryCompιIso P _ (fun _ hX ↦ P.prop_tensor K.2 hX)

/-- The functor `- ⊗ K` on `P` is compatible with `- ⊗ K` on `C` through the inclusion. -/
def tensorRightCompιIso (K : P.FullSubcategory) :
    (curriedTensor P.FullSubcategory).flip.obj K ⋙ P.ι ≅ P.ι ⋙ (curriedTensor C).flip.obj K.obj :=
  Functor.isoWhiskerRight (P.tensorRightIsoLift K).symm P.ι ≪≫
    P.liftFullSubcategoryCompιIso P _ (fun _ hX ↦ P.prop_tensor hX K.2)

/-- The commutation of `K ⊗ -` on `P` with the shifts is that of `K ⊗ -` on `C`. -/
instance commShift_tensorLeftCompιIso_hom (K : P.FullSubcategory)
    [((curriedTensor C).obj K.obj).CommShift A] :
    NatTrans.CommShift (P.tensorLeftCompιIso K).hom A := by
  have : NatTrans.CommShift (P.tensorLeftIsoLift K).hom A :=
    Functor.CommShift.ofIso_compatibility _ _
  have : NatTrans.CommShift (P.tensorLeftIsoLift K).symm.hom A :=
    NatTrans.CommShift.of_iso_inv (P.tensorLeftIsoLift K) A
  dsimp only [tensorLeftCompιIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- The commutation of `- ⊗ K` on `P` with the shifts is that of `- ⊗ K` on `C`. -/
instance commShift_tensorRightCompιIso_hom (K : P.FullSubcategory)
    [((curriedTensor C).flip.obj K.obj).CommShift A] :
    NatTrans.CommShift (P.tensorRightCompιIso K).hom A := by
  have : NatTrans.CommShift (P.tensorRightIsoLift K).hom A :=
    Functor.CommShift.ofIso_compatibility _ _
  have : NatTrans.CommShift (P.tensorRightIsoLift K).symm.hom A :=
    NatTrans.CommShift.of_iso_inv (P.tensorRightIsoLift K) A
  dsimp only [tensorRightCompιIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance

/-- Through the inclusion, the commutation of `K ⊗ -` on `P` with the shifts is that of
`K ⊗ -` on `C`, conjugated by the commutation of the inclusion with the shifts. -/
lemma ι_map_commShiftIso_tensorLeft_hom_app (K : P.FullSubcategory)
    [((curriedTensor C).obj K.obj).CommShift A] (a : A) (X : P.FullSubcategory) :
    P.ι.map ((((curriedTensor P.FullSubcategory).obj K).commShiftIso a).hom.app X) =
      K.obj ◁ (P.ι.commShiftIso a).hom.app X ≫
        (((curriedTensor C).obj K.obj).commShiftIso a).hom.app X.obj ≫
        (P.ι.commShiftIso a).inv.app (K ⊗ X) := by
  have h := NatTrans.shift_app_comm (P.tensorLeftCompιIso K).hom a X
  simp only [Functor.commShiftIso_comp_hom_app, tensorLeftCompιIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, tensorLeftIsoLift, Iso.symm_hom,
    NatIso.ofComponents_inv_app, Iso.refl_inv, liftFullSubcategoryCompιIso, Iso.refl_hom,
    Category.comp_id] at h
  rw [← cancel_mono ((P.ι.commShiftIso a).hom.app (K ⊗ X)), Category.assoc, Category.assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp] at h
  exact h

/-- Through the inclusion, the commutation of `- ⊗ K` on `P` with the shifts is that of
`- ⊗ K` on `C`, conjugated by the commutation of the inclusion with the shifts. -/
lemma ι_map_commShiftIso_tensorRight_hom_app (K : P.FullSubcategory)
    [((curriedTensor C).flip.obj K.obj).CommShift A] (a : A) (X : P.FullSubcategory) :
    P.ι.map ((((curriedTensor P.FullSubcategory).flip.obj K).commShiftIso a).hom.app X) =
      (P.ι.commShiftIso a).hom.app X ▷ K.obj ≫
        (((curriedTensor C).flip.obj K.obj).commShiftIso a).hom.app X.obj ≫
        (P.ι.commShiftIso a).inv.app (X ⊗ K) := by
  have h := NatTrans.shift_app_comm (P.tensorRightCompιIso K).hom a X
  simp only [Functor.commShiftIso_comp_hom_app, tensorRightCompιIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, tensorRightIsoLift, Iso.symm_hom,
    NatIso.ofComponents_inv_app, Iso.refl_inv, liftFullSubcategoryCompιIso, Iso.refl_hom,
    Category.comp_id] at h
  rw [← cancel_mono ((P.ι.commShiftIso a).hom.app (X ⊗ K)), Category.assoc, Category.assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp] at h
  exact h

/-- The computation behind `braiding_hom_commShiftIso_hom_app_of_ι`, for abstract morphisms. -/
private lemma braiding_commShift_aux {D : Type*} [Category D] [MonoidalCategory D]
    [BraidedCategory D] (S : D ⥤ D) {X Y Y' W W' : D} (q : Y' ⟶ S.obj Y)
    (cL : X ⊗ S.obj Y ⟶ S.obj (X ⊗ Y)) (cR : S.obj Y ⊗ X ⟶ S.obj (Y ⊗ X))
    (r₁ : S.obj (X ⊗ Y) ⟶ W) (r₁' : W ⟶ S.obj (X ⊗ Y)) (r₂ : S.obj (Y ⊗ X) ⟶ W')
    (h : (β_ X (S.obj Y)).hom ≫ cR = cL ≫ S.map (β_ X Y).hom) (hr : r₁ ≫ r₁' = 𝟙 _) :
    (β_ X Y').hom ≫ (q ▷ X ≫ cR ≫ r₂) = (X ◁ q ≫ cL ≫ r₁) ≫ (r₁' ≫ S.map (β_ X Y).hom ≫ r₂) := by
  rw [← BraidedCategory.braiding_naturality_right_assoc, reassoc_of% h]
  simp only [Category.assoc, reassoc_of% hr]

variable [BraidedCategory C] [∀ X : C, ((curriedTensor C).obj X).CommShift A]
  [∀ X : C, ((curriedTensor C).flip.obj X).CommShift A]

attribute [local instance] fullBraidedSubcategory

/-- If the braiding of `C` is compatible with the commutations of the tensor product with the
shifts, so is the braiding of the full braided subcategory `P`. -/
lemma braiding_hom_commShiftIso_hom_app_of_ι (a : A)
    (h : ∀ X Y : C, (β_ X (Y⟦a⟧)).hom ≫ (((curriedTensor C).flip.obj X).commShiftIso a).hom.app Y =
      (((curriedTensor C).obj X).commShiftIso a).hom.app Y ≫ ((β_ X Y).hom)⟦a⟧')
    (X Y : P.FullSubcategory) :
    (β_ X (Y⟦a⟧)).hom ≫
        (((curriedTensor P.FullSubcategory).flip.obj X).commShiftIso a).hom.app Y =
      (((curriedTensor P.FullSubcategory).obj X).commShiftIso a).hom.app Y ≫
        ((β_ X Y).hom)⟦a⟧' := by
  apply P.fullyFaithfulι.map_injective
  rw [Functor.map_comp, Functor.map_comp, ι_map_commShiftIso_tensorRight_hom_app,
    ι_map_commShiftIso_tensorLeft_hom_app]
  have hN : P.ι.map ((shiftFunctor P.FullSubcategory a).map (β_ X Y).hom) =
      (P.ι.commShiftIso a).hom.app (X ⊗ Y) ≫ (shiftFunctor C a).map (β_ X.obj Y.obj).hom ≫
        (P.ι.commShiftIso a).inv.app (Y ⊗ X) := by
    rw [← cancel_mono ((P.ι.commShiftIso a).hom.app (Y ⊗ X)), Category.assoc, Category.assoc,
      Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact P.ι.commShiftIso_hom_naturality (β_ X Y).hom a
  rw [hN]
  exact braiding_commShift_aux (shiftFunctor C a) _ _ _ _ _ _ (h X.obj Y.obj)
    ((P.ι.commShiftIso a).inv_hom_id_app (X ⊗ Y))

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]
  {A : Type*} [AddMonoid A] [HasShift C A] [P.IsStableUnderShift A]
  [∀ X : C, ((curriedTensor C).obj X).CommShift A]
  [∀ X : C, ((curriedTensor C).flip.obj X).CommShift A]

set_option synthInstance.maxSize 4096 in
-- the instance problems for the composite functors are large
/-- The associator of `P`, natural in its middle variable, commutes with the shifts if that of
`C` does. -/
lemma commShift_associatorNatTrans₂ (X Z : P.FullSubcategory)
    [NatTrans.CommShift (associatorNatTrans₂ C X.obj Z.obj) A] :
    NatTrans.CommShift (associatorNatTrans₂ P.FullSubcategory X Z) A := by
  have : P.ι.Faithful := P.faithful_ι
  let eF : ((curriedTensor P.FullSubcategory).obj X ⋙ (curriedTensor _).flip.obj Z) ⋙ P.ι ≅
      P.ι ⋙ ((curriedTensor C).obj X.obj ⋙ (curriedTensor C).flip.obj Z.obj) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (P.tensorRightCompιIso Z) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (P.tensorLeftCompιIso X) _ ≪≫
      Functor.associator _ _ _
  let eG : ((curriedTensor P.FullSubcategory).flip.obj Z ⋙ (curriedTensor _).obj X) ⋙ P.ι ≅
      P.ι ⋙ ((curriedTensor C).flip.obj Z.obj ⋙ (curriedTensor C).obj X.obj) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (P.tensorLeftCompιIso X) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (P.tensorRightCompιIso Z) _ ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift eF.hom A := by
    dsimp only [eF, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  have : NatTrans.CommShift eG.inv A := by
    have : NatTrans.CommShift eG.hom A := by
      dsimp only [eG, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Iso.symm_hom]
      infer_instance
    exact NatTrans.CommShift.of_iso_inv eG A
  have e : Functor.whiskerRight (associatorNatTrans₂ P.FullSubcategory X Z) P.ι =
      eF.hom ≫ Functor.whiskerLeft P.ι (associatorNatTrans₂ C X.obj Z.obj) ≫ eG.inv := by
    ext Y
    simp only [Functor.comp_obj, curriedTensor_obj_obj, Functor.flip_obj_obj, ι_obj,
      tensorObj_obj, Functor.whiskerRight_app, associatorNatTrans₂_app, associator_def,
      isoMk_hom, ι_map, homMk_hom, tensorRightCompιIso, tensorRightIsoLift,
      liftFullSubcategoryCompιIso, Iso.trans_refl, tensorLeftCompιIso, tensorLeftIsoLift,
      Functor.isoWhiskerRight_twice, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, Iso.trans_inv,
      Iso.symm_inv, Functor.isoWhiskerRight_inv, Category.assoc, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      NatIso.ofComponents_inv_app, Iso.refl_inv, FullSubcategory.id_hom, Functor.comp_map,
      Functor.flip_obj_map, curriedTensor_map_app, Functor.associator_inv_app,
      NatIso.ofComponents_hom_app, Iso.refl_hom, curriedTensor_obj_map, whiskerLeft_id,
      Category.comp_id, Category.id_comp, eF, eG]
    erw [Category.id_comp, MonoidalCategory.id_whiskerRight, Category.id_comp, Category.id_comp,
      Category.comp_id]
  have : NatTrans.CommShift (Functor.whiskerRight (associatorNatTrans₂ P.FullSubcategory X Z)
      P.ι) A := by
    rw [e]
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ P.ι

end CategoryTheory.ObjectProperty

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift

/-! # The signed derived braiding commutes with coefficient shifts

Source: Stacks Project, More on Algebra, Tag 0BYI,
signed cochain tensor convention.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

variable (C : Type uC) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_derivedTensorBraidingShift : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory C] in
private theorem cochain_braiding_shift (K M : CochainComplex C ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctorShift₂Iso K M (curriedTensor C) n).hom ≫
      (β_ K M).hom⟦n⟧' =
    (β_ K (M⟦n⟧)).hom ≫
      (CochainComplex.mapBifunctorShift₁Iso M K (curriedTensor C) n).hom := by
  ext j : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have h' : p + q = j := h
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f_assoc K M (curriedTensor C) n
    p q j h (q + n) (j + n) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id, curriedTensor_obj_map,
    CochainComplex.shiftFunctor_map_f']
  erw [whiskerLeft_id, Category.id_comp]
  simp only [Units.smul_def, Preadditive.zsmul_comp]
  erw [CochainComplex.Monoidal.ι_braiding_hom]
  erw [CochainComplex.Monoidal.ι_braiding_hom_assoc]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f M K (curriedTensor C) n
    q p j (by omega) (q + n) (j + n) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id, curriedTensor_map_app]
  erw [id_whiskerRight, Category.id_comp]
  have hs : ((p * n).negOnePow : ℤ) * ((p * (q + n)).negOnePow : ℤ) =
      ((p * q).negOnePow : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add]
    have he : p * n + p * (q + n) = p * q + 2 * (p * n) := by ring
    rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  simp only [smul_smul, hs]
  rfl

omit [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory C] in
open TensorCommShift₂ in
private theorem cochain_braiding_commShift (K : CochainComplex C ℤ) :
    NatTrans.CommShift ((BraidedCategory.curriedBraidingNatIso _).hom.app K) ℤ where
  shift_comm n := by
    refine NatTrans.ext (funext fun M => ?_)
    exact cochain_braiding_shift C K M n

open TensorCommShift₂ in
private theorem derived_braiding_kflat (P : CochainComplex.KFlat C) :
    NatTrans.CommShift ((canonicalTensorSymmetry C).hom.app ((LKFlat C).obj P)) ℤ := by
  let : BraidedCategory (DerivedCategory C) := braidedCategory' C
  have := cochain_braiding_commShift C P.obj
  apply commShift_of_whiskerLeft_L _ (tensorLeftLift P) (tensorRightLift P)
    (Functor.whiskerRight ((BraidedCategory.curriedBraidingNatIso _).hom.app P.obj) (L C))
  ext M
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app,
    tensorLeftLift_app, tensorRightLift_app]
  exact CategoryTheory.DerivedMonoidal.braiding_hom_μ Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C _).obj P.obj) ((HomotopyCategory.quotient C _).obj M)

/-- The canonical signed symmetry intertwines the two canonical tensor shifts.
Source: Stacks Project, More on Algebra, Tag 0BYI (signed tensor symmetry).
(blueprint: lem-pur-derived-tensor-braiding-shift).

Proof. On each cochain summand, the shift sign times the shifted Koszul sign is
its unshifted Koszul sign. The identity descends through the tensor comparison
for a K-flat first factor. Every derived object is isomorphic to such an image;
naturality transports the identity to that object. -/
theorem canonicalTensorSymmetry_commShift (K : DerivedCategory C) :
    NatTrans.CommShift ((canonicalTensorSymmetry C).hom.app K) ℤ := by
  have := Localization.essSurj (TensorCommShift₂.LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  let P := (TensorCommShift₂.LKFlat C).objPreimage K
  let e := (TensorCommShift₂.LKFlat C).objObjPreimageIso K
  have := derived_braiding_kflat C P
  have he : (canonicalTensorSymmetry C).hom.app K =
      (curriedTensor _).map e.inv ≫
        (canonicalTensorSymmetry C).hom.app ((TensorCommShift₂.LKFlat C).obj P) ≫
        (curriedTensor _).flip.map e.hom := by
    symm
    rw [← Category.assoc, (canonicalTensorSymmetry C).hom.naturality e.inv,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [he]
  infer_instance

end DerivedCategory

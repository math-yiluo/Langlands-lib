/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The associator of cochain complexes commutes with shifts

For cochain complexes `K`, `L`, `M` indexed by `ℤ`, the associator
`(K ⊗ L) ⊗ M ≅ K ⊗ (L ⊗ M)` is compatible with the identifications of total complexes
`CochainComplex.mapBifunctorShift₁Iso` (moving a shift of the first factor out, without sign)
and `CochainComplex.mapBifunctorShift₂Iso` (moving a shift of the second factor out, with the
sign `(-1) ^ (p * n)` on the summand of degree `p` in the first factor), for a shift of each of
the three factors. No sign appears: on a summand `K.X p ⊗ L.X q ⊗ M.X r`, both sides carry the
Koszul sign of the shift passing the factors on its left.

## Main statements

- `CochainComplex.associator_hom_comp_mapBifunctorShift₁Iso_hom`: shift of the first factor.
- `CochainComplex.associator_hom_comp_whiskerLeft_mapBifunctorShift₁Iso_hom`: shift of the
  second factor.
- `CochainComplex.associator_hom_comp_whiskerLeft_mapBifunctorShift₂Iso_hom`: shift of the third
  factor.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

open Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (K L M : CochainComplex C ℤ)

/-- The associator commutes with the shift of the first factor:
`(K⟦a⟧ ⊗ L) ⊗ M ≅ K⟦a⟧ ⊗ (L ⊗ M) ≅ (K ⊗ (L ⊗ M))⟦a⟧` is
`(K⟦a⟧ ⊗ L) ⊗ M ≅ (K ⊗ L)⟦a⟧ ⊗ M ≅ ((K ⊗ L) ⊗ M)⟦a⟧ ≅ (K ⊗ (L ⊗ M))⟦a⟧`. -/
lemma associator_hom_comp_mapBifunctorShift₁Iso_hom (a : ℤ) :
    (α_ (K⟦a⟧) L M).hom ≫ (mapBifunctorShift₁Iso K (L ⊗ M) (curriedTensor C) a).hom =
      (mapBifunctorShift₁Iso K L (curriedTensor C) a).hom ▷ M ≫
        (mapBifunctorShift₁Iso (K ⊗ L) M (curriedTensor C) a).hom ≫ (α_ K L M).hom⟦a⟧' := by
  ext n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = n := h
  simp only [HomologicalComplex.comp_f]
  erw [ι₁₂_associator_hom_assoc]
  rw [ι₁₂_eq (K⟦a⟧) L M p q r (p + q) n rfl h', ι₂₃_eq (K⟦a⟧) L M p q r (q + r) n rfl (by omega)]
  simp only [assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ p (q + r) n (by omega) (p + a) (n + a) rfl rfl]
  erw [ι_whiskerRight_assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ (p + q) r n (by omega) (p + q + a) (n + a)
    rfl rfl]
  rw [← comp_whiskerRight_assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ p q (p + q) rfl (p + a) (p + q + a) rfl
    (by omega)]
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    id_comp, comp_id]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  erw [NatTrans.id_app, NatTrans.id_app, NatTrans.id_app]
  erw [id_comp, id_comp, id_comp]
  erw [← ι₂₃_eq K L M (p + a) q r (q + r) (n + a) rfl (by omega)]
  have e := ι₁₂_associator_hom K L M (p + a) q r (n + a) (by omega)
  rw [ι₁₂_eq K L M (p + a) q r (p + q + a) (n + a) (by omega) (by omega), assoc] at e
  exact e.symm


/-- The associator commutes with the shift of the second factor:
`(K ⊗ L⟦b⟧) ⊗ M ≅ K ⊗ (L⟦b⟧ ⊗ M) ≅ K ⊗ (L ⊗ M)⟦b⟧ ≅ (K ⊗ (L ⊗ M))⟦b⟧` is
`(K ⊗ L⟦b⟧) ⊗ M ≅ (K ⊗ L)⟦b⟧ ⊗ M ≅ ((K ⊗ L) ⊗ M)⟦b⟧ ≅ (K ⊗ (L ⊗ M))⟦b⟧`. -/
lemma associator_hom_comp_whiskerLeft_mapBifunctorShift₁Iso_hom (b : ℤ) :
    (α_ K (L⟦b⟧) M).hom ≫ K ◁ (mapBifunctorShift₁Iso L M (curriedTensor C) b).hom ≫
        (mapBifunctorShift₂Iso K (L ⊗ M) (curriedTensor C) b).hom =
      (mapBifunctorShift₂Iso K L (curriedTensor C) b).hom ▷ M ≫
        (mapBifunctorShift₁Iso (K ⊗ L) M (curriedTensor C) b).hom ≫ (α_ K L M).hom⟦b⟧' := by
  ext n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = n := h
  simp only [HomologicalComplex.comp_f]
  erw [ι₁₂_associator_hom_assoc]
  rw [ι₁₂_eq K (L⟦b⟧) M p q r (p + q) n rfl h', ι₂₃_eq K (L⟦b⟧) M p q r (q + r) n rfl (by omega)]
  simp only [assoc]
  erw [ιTensorObj_whiskerLeft_f_assoc]
  rw [← whiskerLeft_comp_assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ q r (q + r) rfl (q + b) (q + r + b) rfl (by omega)]
  erw [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ p (q + r) n (by omega) (q + r + b) (n + b) rfl
    (by omega)]
  erw [ι_whiskerRight_assoc]
  erw [ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ (p + q) r n (by omega) (p + q + b) (n + b)
    rfl rfl]
  rw [← comp_whiskerRight_assoc]
  erw [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ p q (p + q) rfl (q + b) (p + q + b) rfl
    (by omega)]
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    comp_id]
  simp only [id_comp, Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    zsmul_whiskerRight]
  congr 1
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [NatTrans.id_app]
  repeat erw [id_comp]
  erw [← ι₂₃_eq K L M p (q + b) r (q + r + b) (n + b) (by omega) (by omega)]
  have e := ι₁₂_associator_hom K L M p (q + b) r (n + b) (by omega)
  rw [ι₁₂_eq K L M p (q + b) r (p + q + b) (n + b) (by omega) (by omega), assoc] at e
  exact e.symm

/-- The associator commutes with the shift of the third factor:
`(K ⊗ L) ⊗ M⟦c⟧ ≅ K ⊗ (L ⊗ M⟦c⟧) ≅ K ⊗ (L ⊗ M)⟦c⟧ ≅ (K ⊗ (L ⊗ M))⟦c⟧` is
`(K ⊗ L) ⊗ M⟦c⟧ ≅ ((K ⊗ L) ⊗ M)⟦c⟧ ≅ (K ⊗ (L ⊗ M))⟦c⟧`. -/
lemma associator_hom_comp_whiskerLeft_mapBifunctorShift₂Iso_hom (c : ℤ) :
    (α_ K L (M⟦c⟧)).hom ≫ K ◁ (mapBifunctorShift₂Iso L M (curriedTensor C) c).hom ≫
        (mapBifunctorShift₂Iso K (L ⊗ M) (curriedTensor C) c).hom =
      (mapBifunctorShift₂Iso (K ⊗ L) M (curriedTensor C) c).hom ≫ (α_ K L M).hom⟦c⟧' := by
  ext n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have h' : p + q + r = n := h
  simp only [HomologicalComplex.comp_f]
  erw [ι₁₂_associator_hom_assoc]
  rw [ι₁₂_eq K L (M⟦c⟧) p q r (p + q) n rfl h', ι₂₃_eq K L (M⟦c⟧) p q r (q + r) n rfl (by omega)]
  simp only [assoc]
  erw [ιTensorObj_whiskerLeft_f_assoc]
  rw [← whiskerLeft_comp_assoc]
  erw [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ q r (q + r) rfl (r + c) (q + r + c) rfl (by omega)]
  erw [ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ p (q + r) n (by omega) (q + r + c) (n + c) rfl
    (by omega)]
  erw [ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ (p + q) r n (by omega) (r + c) (n + c)
    rfl rfl]
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    comp_id]
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.zsmul_comp, whiskerLeft_zsmul,
    smul_smul]
  rw [show (((p * c).negOnePow : ℤ) * ((q * c).negOnePow : ℤ)) = (((p + q) * c).negOnePow : ℤ)
    by rw [add_mul, Int.negOnePow_add, Units.val_mul]]
  congr 1
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [id_comp]
  erw [← ι₂₃_eq K L M p q (r + c) (q + r + c) (n + c) (by omega) (by omega)]
  have e := ι₁₂_associator_hom K L M p q (r + c) (n + c) (by omega)
  rw [ι₁₂_eq K L M p q (r + c) (p + q) (n + c) rfl (by omega), assoc] at e
  exact e.symm

end CochainComplex

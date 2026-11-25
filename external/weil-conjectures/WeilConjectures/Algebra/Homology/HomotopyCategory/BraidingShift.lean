/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.Algebra.Homology.Monoidal.BraidingShift
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated

/-!
# The Koszul braiding of the homotopy category commutes with the shifts

For `K L` in the homotopy category `K(C)`, the square
```
K ⊗ L⟦y⟧ ──── β ────▶ L⟦y⟧ ⊗ K
   │                     │
   ▼                     ▼
(K ⊗ L)⟦y⟧ ──β⟦y⟧──▶ (L ⊗ K)⟦y⟧
```
commutes, the vertical maps being the commutations of `K ⊗ -` and `- ⊗ K` with the shifts
(`HomotopyCategory.braiding_hom_commShiftIso_hom_app`). It is the image under the quotient functor
of the corresponding statement for cochain complexes
(`CochainComplex.Monoidal.braiding_hom_mapBifunctorShift₁Iso_hom`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace HomotopyCategory

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

omit [BraidedCategory C] in
/-- On images of complexes, the commutation of `K ⊗ -` with the shifts is that of complexes. -/
lemma tensorLeft_commShiftIso_hom_app_quotient (K L : CochainComplex C ℤ) (y : ℤ) :
    (((curriedTensor (HomotopyCategory C (.up ℤ))).obj ((quotient C _).obj K)).commShiftIso
        y).hom.app ((quotient C _).obj L) =
      ((quotient C _).obj K) ◁ ((quotient C (.up ℤ)).commShiftIso y).inv.app L ≫
        (quotient C _).map (CochainComplex.mapBifunctorShift₂Iso K L (curriedTensor C) y).hom ≫
        ((quotient C (.up ℤ)).commShiftIso y).hom.app (K ⊗ L) := by
  have h := NatTrans.shift_app_comm ((curriedTensor C).quotientCompBifunctorMapHomotopyObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) K).hom y L
  simp only [Functor.commShiftIso_comp_hom_app, Functor.quotientCompBifunctorMapHomotopyObjIso,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [← cancel_epi (((curriedTensor (HomotopyCategory C (.up ℤ))).obj
    ((quotient C _).obj K)).map (((quotient C (.up ℤ)).commShiftIso y).hom.app L))]
  refine (Category.comp_id _).symm.trans (h.trans ?_)
  erw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id_app,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rfl

omit [BraidedCategory C] in
/-- On images of complexes, the commutation of `- ⊗ K` with the shifts is that of complexes. -/
lemma tensorRight_commShiftIso_hom_app_quotient (K L : CochainComplex C ℤ) (y : ℤ) :
    (((curriedTensor (HomotopyCategory C (.up ℤ))).flip.obj ((quotient C _).obj K)).commShiftIso
        y).hom.app ((quotient C _).obj L) =
      ((quotient C (.up ℤ)).commShiftIso y).inv.app L ▷ ((quotient C _).obj K) ≫
        (quotient C _).map (CochainComplex.mapBifunctorShift₁Iso L K (curriedTensor C) y).hom ≫
        ((quotient C (.up ℤ)).commShiftIso y).hom.app (L ⊗ K) := by
  have h := NatTrans.shift_app_comm ((curriedTensor C).quotientCompBifunctorMapHomotopyFlipObjIso
    (.up ℤ) (.up ℤ) (.up ℤ) K).hom y L
  simp only [Functor.commShiftIso_comp_hom_app,
    Functor.quotientCompBifunctorMapHomotopyFlipObjIso, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [← cancel_epi (((curriedTensor (HomotopyCategory C (.up ℤ))).flip.obj
    ((quotient C _).obj K)).map (((quotient C (.up ℤ)).commShiftIso y).hom.app L))]
  refine (Category.comp_id _).symm.trans (h.trans ?_)
  erw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id_app,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  rfl

/-- **The Koszul braiding of the homotopy category commutes with the shifts.** -/
@[reassoc]
lemma braiding_hom_commShiftIso_hom_app (K L : HomotopyCategory C (.up ℤ)) (y : ℤ) :
    (β_ K (L⟦y⟧)).hom ≫ (((curriedTensor _).flip.obj K).commShiftIso y).hom.app L =
      (((curriedTensor _).obj K).commShiftIso y).hom.app L ≫ ((β_ K L).hom)⟦y⟧' := by
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
  rw [tensorLeft_commShiftIso_hom_app_quotient, tensorRight_commShiftIso_hom_app_quotient,
    ← BraidedCategory.braiding_naturality_right_assoc, Category.assoc, Category.assoc, cancel_epi]
  have hC := (quotient C (.up ℤ)).congr_map
    (CochainComplex.Monoidal.braiding_hom_mapBifunctorShift₁Iso_hom K L y)
  simp only [Functor.map_comp] at hC
  erw [reassoc_of% hC]
  rw [cancel_epi]
  exact (quotient C (.up ℤ)).commShiftIso_hom_naturality
    (CochainComplex.Monoidal.braiding K L).hom y

end HomotopyCategory

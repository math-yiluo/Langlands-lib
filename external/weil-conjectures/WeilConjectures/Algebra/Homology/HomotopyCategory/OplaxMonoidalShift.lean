/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated
public import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# The comonoidal comparison on homotopy categories commutes with shifts

Let `G : C ⥤ D` be an additive oplax monoidal functor which preserves the coproducts defining
the tensor product of cochain complexes. The comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` on homotopy
categories (`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans`) commutes with
the shifts in each variable.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

set_option backward.isDefEq.respectTransparency false in
/-- For a fixed `K`, the comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` on homotopy categories commutes
with the shifts in `L`. -/
instance commShift_mapHomotopyCategoryδNatTrans_app (K : HomotopyCategory C (.up ℤ)) :
    NatTrans.CommShift (F₁ := (curriedTensor _).obj K ⋙ G.mapHomotopyCategory (.up ℤ))
      (F₂ := G.mapHomotopyCategory (.up ℤ) ⋙
        (curriedTensor _).obj ((G.mapHomotopyCategory (.up ℤ)).obj K))
      ((mapHomotopyCategoryδNatTrans (.up ℤ) G).app K) ℤ := by
  obtain ⟨K₀⟩ := K
  let δK : (curriedTensor (HomotopyCategory C (.up ℤ))).obj ⟨K₀⟩ ⋙ G.mapHomotopyCategory (.up ℤ) ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ (curriedTensor _).obj
        ((G.mapHomotopyCategory (.up ℤ)).obj ⟨K₀⟩) :=
    (mapHomotopyCategoryδNatTrans (.up ℤ) G).app ⟨K₀⟩
  change NatTrans.CommShift δK ℤ
  let e₁ : HomotopyCategory.quotient C (.up ℤ) ⋙
      ((curriedTensor (HomotopyCategory C (.up ℤ))).obj ⟨K₀⟩ ⋙ G.mapHomotopyCategory (.up ℤ)) ≅
      ((curriedTensor C).map₂CochainComplex.obj K₀ ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
        HomotopyCategory.quotient D (.up ℤ) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((curriedTensor C).quotientCompBifunctorMapHomotopyObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) K₀) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (G.mapHomotopyCategoryFactors (.up ℤ)) ≪≫
      (Functor.associator _ _ _).symm
  let e₂ : HomotopyCategory.quotient C (.up ℤ) ⋙ (G.mapHomotopyCategory (.up ℤ) ⋙
      (curriedTensor (HomotopyCategory D (.up ℤ))).obj
        ((G.mapHomotopyCategory (.up ℤ)).obj ⟨K₀⟩)) ≅
      (G.mapHomologicalComplex (.up ℤ) ⋙ (curriedTensor D).map₂CochainComplex.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj K₀)) ⋙ HomotopyCategory.quotient D (.up ℤ) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((curriedTensor D).quotientCompBifunctorMapHomotopyObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) ((G.mapHomologicalComplex (.up ℤ)).obj K₀)) ≪≫
      (Functor.associator _ _ _).symm
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by
    dsimp only [e₂, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
    infer_instance
  let δ' : (curriedTensor C).map₂CochainComplex.obj K₀ ⋙ G.mapHomologicalComplex (.up ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ (curriedTensor D).map₂CochainComplex.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj K₀) :=
    (mapHomologicalComplexδNatTrans (.up ℤ) G).app K₀
  have : NatTrans.CommShift δ' ℤ :=
    HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_app (δNatTrans G) K₀
  have eq : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      δK =
      e₁.hom ≫ Functor.whiskerRight δ' (HomotopyCategory.quotient D (.up ℤ)) ≫ e₂.inv := by
    ext L
    simp only [comp_obj, curriedTensor_obj_obj, whiskerLeft_app,
      quotientCompBifunctorMapHomotopyObjIso, isoWhiskerRight_refl, mapHomotopyCategoryFactors,
      Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, isoWhiskerLeft_hom, Iso.trans_inv, Iso.symm_inv,
      isoWhiskerLeft_inv, Iso.refl_inv, assoc, isoWhiskerRight_inv, NatTrans.comp_app,
      associator_inv_app, NatTrans.id_app, associator_hom_app, Quotient.lift.isLift_hom,
      whiskerRight_app, mapHomologicalComplexδNatTrans_app_app, Quotient.lift.isLift_inv,
      curriedTensor_obj_map, MonoidalCategory.whiskerLeft_id, comp_id, id_comp, δK, e₁, δ', e₂]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      δK) ℤ := by
    rw [eq]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun L ↦ ⟨L.as, 𝟙 _, inferInstance⟩)

set_option backward.isDefEq.respectTransparency false in
/-- For a fixed `K`, the comparison `G(L ⊗ K) ⟶ G(L) ⊗ G(K)` on homotopy categories commutes
with the shifts in `L`. -/
instance commShift_mapHomotopyCategoryδNatTrans_flipApp (K : HomotopyCategory C (.up ℤ)) :
    NatTrans.CommShift (F₁ := (curriedTensor _).flip.obj K ⋙ G.mapHomotopyCategory (.up ℤ))
      (F₂ := G.mapHomotopyCategory (.up ℤ) ⋙
        (curriedTensor _).flip.obj ((G.mapHomotopyCategory (.up ℤ)).obj K))
      ((mapHomotopyCategoryδNatTrans (.up ℤ) G).flipApp K) ℤ := by
  obtain ⟨K₀⟩ := K
  let δK : (curriedTensor (HomotopyCategory C (.up ℤ))).flip.obj ⟨K₀⟩ ⋙
      G.mapHomotopyCategory (.up ℤ) ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ (curriedTensor _).flip.obj
        ((G.mapHomotopyCategory (.up ℤ)).obj ⟨K₀⟩) :=
    (mapHomotopyCategoryδNatTrans (.up ℤ) G).flipApp ⟨K₀⟩
  change NatTrans.CommShift δK ℤ
  let e₁ : HomotopyCategory.quotient C (.up ℤ) ⋙
      ((curriedTensor (HomotopyCategory C (.up ℤ))).flip.obj ⟨K₀⟩ ⋙ G.mapHomotopyCategory (.up ℤ)) ≅
      ((curriedTensor C).map₂CochainComplex.flip.obj K₀ ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
        HomotopyCategory.quotient D (.up ℤ) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((curriedTensor C).quotientCompBifunctorMapHomotopyFlipObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) K₀) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (G.mapHomotopyCategoryFactors (.up ℤ)) ≪≫
      (Functor.associator _ _ _).symm
  let e₂ : HomotopyCategory.quotient C (.up ℤ) ⋙ (G.mapHomotopyCategory (.up ℤ) ⋙
      (curriedTensor (HomotopyCategory D (.up ℤ))).flip.obj
        ((G.mapHomotopyCategory (.up ℤ)).obj ⟨K₀⟩)) ≅
      (G.mapHomologicalComplex (.up ℤ) ⋙ (curriedTensor D).map₂CochainComplex.flip.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj K₀)) ⋙ HomotopyCategory.quotient D (.up ℤ) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((curriedTensor D).quotientCompBifunctorMapHomotopyFlipObjIso
        (.up ℤ) (.up ℤ) (.up ℤ) ((G.mapHomologicalComplex (.up ℤ)).obj K₀)) ≪≫
      (Functor.associator _ _ _).symm
  have : NatTrans.CommShift e₁.hom ℤ := by dsimp [e₁]; infer_instance
  have : NatTrans.CommShift e₂.hom ℤ := by
    dsimp only [e₂, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
    infer_instance
  let δ' : (curriedTensor C).map₂CochainComplex.flip.obj K₀ ⋙ G.mapHomologicalComplex (.up ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ (curriedTensor D).map₂CochainComplex.flip.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj K₀) :=
    (mapHomologicalComplexδNatTrans (.up ℤ) G).flipApp K₀
  have : NatTrans.CommShift δ' ℤ :=
    HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_flipApp (δNatTrans G) K₀
  have eq : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      δK =
      e₁.hom ≫ Functor.whiskerRight δ' (HomotopyCategory.quotient D (.up ℤ)) ≫ e₂.inv := by
    ext L
    simp only [comp_obj, flip_obj_obj, curriedTensor_obj_obj, whiskerLeft_app,
      flipFunctor_map_app_app, quotientCompBifunctorMapHomotopyFlipObjIso, isoWhiskerRight_refl,
      mapHomotopyCategoryFactors, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, isoWhiskerLeft_hom,
      Iso.trans_inv, Iso.symm_inv, isoWhiskerLeft_inv, Iso.refl_inv, assoc, isoWhiskerRight_inv,
      NatTrans.comp_app, associator_inv_app, NatTrans.id_app, associator_hom_app,
      Quotient.lift.isLift_hom, whiskerRight_app, mapHomologicalComplexδNatTrans_app_app,
      Quotient.lift.isLift_inv, flip_obj_map, map_id, comp_id, id_comp, δK, e₁, δ', e₂]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      δK) ℤ := by
    rw [eq]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun L ↦ ⟨L.as, 𝟙 _, inferInstance⟩)

end CategoryTheory.Functor.OplaxMonoidal

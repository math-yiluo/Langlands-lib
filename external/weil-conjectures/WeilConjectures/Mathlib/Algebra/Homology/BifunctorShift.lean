/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-!
# The comparison of total complexes commutes with shifts

Let `F : C₁ ⥤ C₂ ⥤ D` and `F' : C₁' ⥤ C₂' ⥤ D'` be bifunctors, `G₁ : C₁ ⥤ C₁'`,
`G₂ : C₂ ⥤ C₂'` and `G : D ⥤ D'` additive functors and
`τ : G (F X₁ X₂) ⟶ F' (G₁ X₁) (G₂ X₂)` a natural transformation. The comparison
`HomologicalComplex.mapBifunctorComparison τ (.up ℤ) K₁ K₂ :
  G(mapBifunctor K₁ K₂ F) ⟶ mapBifunctor (G₁ K₁) (G₂ K₂) F'` of cochain complexes commutes with
the shifts in each variable: for fixed `K₁` (resp. `K₂`) it is a natural transformation
commuting with the shifts by `ℤ`, for the shift compatibilities
`CochainComplex.mapBifunctorShift₂Iso` (resp. `CochainComplex.mapBifunctorShift₁Iso`) of
total complexes and the shift compatibilities of `G.mapHomologicalComplex`.

The unit `𝟙_` of cochain complexes is concentrated in degree `0`, so that no sign appears when
the shift of the second factor of `𝟙_ ⊗ K` is moved out
(`CochainComplex.mapBifunctorShift₂Iso_hom_leftUnitor_hom`); the shift of the first factor of
`K ⊗ 𝟙_` is moved out without sign (`CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom`).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* C₁'] [Category* C₂'] [Category* D']
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [Preadditive C₁'] [Preadditive C₂'] [Preadditive D']
  {F : C₁ ⥤ C₂ ⥤ D} [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  {F' : C₁' ⥤ C₂' ⥤ D'} [F'.Additive] [∀ X₁, (F'.obj X₁).Additive]
  {G₁ : C₁ ⥤ C₁'} {G₂ : C₂ ⥤ C₂'} {G : D ⥤ D'}
  [G₁.Additive] [G₂.Additive] [G.Additive]
  (τ : (Functor.postcompose₂.obj G).obj F ⟶ (((Functor.whiskeringLeft₂ D').obj G₁).obj G₂).obj F')
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), CochainComplex.HasMapBifunctor K₁ K₂ F]
  [∀ (K₁ : CochainComplex C₁' ℤ) (K₂ : CochainComplex C₂' ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ F']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a fixed cochain complex `K₁`, the comparison `G(mapBifunctor K₁ K₂ F) ⟶
mapBifunctor (G₁ K₁) (G₂ K₂) F'` commutes with the shifts in `K₂`. -/
instance commShift_mapBifunctorComparisonNatTrans_app (K₁ : CochainComplex C₁ ℤ) :
    NatTrans.CommShift (F₁ := F.map₂CochainComplex.obj K₁ ⋙ G.mapHomologicalComplex (.up ℤ))
      (F₂ := G₂.mapHomologicalComplex (.up ℤ) ⋙
        F'.map₂CochainComplex.obj ((G₁.mapHomologicalComplex (.up ℤ)).obj K₁))
      ((mapBifunctorComparisonNatTrans τ (.up ℤ)).app K₁) ℤ where
  shift_comm n := by
    ext K₂ j
    refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
    dsimp
    simp only [Functor.commShiftIso_comp_hom_app,
      Functor.commShiftIso_map₂CochainComplex_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.assoc]
    erw [Category.id_comp]
    rw [← G.map_comp_assoc]
    erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + n) (j + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Iso.refl_inv, Category.comp_id, map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    erw [ι_mapBifunctorMap_assoc,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + n) (j + n) rfl rfl]
    simp only [Units.smul_def, CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id, Functor.map_zsmul,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f, NatTrans.id_app,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    congr 1
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      map_ιMapBifunctor_mapBifunctorComparisonX]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.id_comp]
    erw [Category.id_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a fixed cochain complex `K₂`, the comparison `G(mapBifunctor K₁ K₂ F) ⟶
mapBifunctor (G₁ K₁) (G₂ K₂) F'` commutes with the shifts in `K₁`. -/
instance commShift_mapBifunctorComparisonNatTrans_flipApp (K₂ : CochainComplex C₂ ℤ) :
    NatTrans.CommShift (F₁ := F.map₂CochainComplex.flip.obj K₂ ⋙ G.mapHomologicalComplex (.up ℤ))
      (F₂ := G₁.mapHomologicalComplex (.up ℤ) ⋙
        F'.map₂CochainComplex.flip.obj ((G₂.mapHomologicalComplex (.up ℤ)).obj K₂))
      ((mapBifunctorComparisonNatTrans τ (.up ℤ)).flipApp K₂) ℤ where
  shift_comm n := by
    ext K₁ j
    refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
    dsimp
    simp only [Functor.commShiftIso_comp_hom_app,
      Functor.commShiftIso_map₂CochainComplex_flip_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.assoc]
    erw [Category.id_comp]
    rw [← G.map_comp_assoc]
    erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + n) (j + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Iso.refl_inv, Category.comp_id, map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    erw [ι_mapBifunctorMap_assoc,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + n) (j + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Iso.refl_inv, Category.comp_id, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      map_ιMapBifunctor_mapBifunctorComparisonX]
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    erw [Category.id_comp]
    erw [Category.id_comp]
    rfl

end HomologicalComplex

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (K : CochainComplex C ℤ) (n : ℤ)

lemma leftUnitor_inv_mapBifunctorShift₂Iso_hom :
    (λ_ (K⟦n⟧)).inv ≫ (mapBifunctorShift₂Iso (𝟙_ (CochainComplex C ℤ)) K (curriedTensor C) n).hom =
      (λ_ K).inv⟦n⟧' := by
  ext i
  change (HomologicalComplex.leftUnitor' (K⟦n⟧)).inv i ≫ _ =
    (HomologicalComplex.leftUnitor' K).inv (i + n)
  rw [HomologicalComplex.leftUnitor'_inv, HomologicalComplex.leftUnitor'_inv]
  have h := ι_mapBifunctorShift₂Iso_hom_f (𝟙_ (CochainComplex C ℤ)) K (curriedTensor C) n 0 i i
    (zero_add i) (i + n) (i + n) rfl rfl
  erw [assoc, assoc, h]
  simp only [shiftFunctor_obj_X', curriedTensor_obj_obj, zero_mul, Int.negOnePow_zero,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_obj_map,
    Iso.refl_inv, comp_id, one_smul, Iso.cancel_iso_inv_left]
  erw [MonoidalCategory.whiskerLeft_id, id_comp]
  rfl

lemma mapBifunctorShift₂Iso_hom_leftUnitor_hom :
    (mapBifunctorShift₂Iso (𝟙_ (CochainComplex C ℤ)) K (curriedTensor C) n).hom ≫
      (λ_ K).hom⟦n⟧' = (λ_ (K⟦n⟧)).hom := by
  rw [← cancel_epi (λ_ (K⟦n⟧)).inv, reassoc_of% leftUnitor_inv_mapBifunctorShift₂Iso_hom,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Iso.inv_hom_id]

lemma rightUnitor_inv_mapBifunctorShift₁Iso_hom :
    (ρ_ (K⟦n⟧)).inv ≫ (mapBifunctorShift₁Iso K (𝟙_ (CochainComplex C ℤ)) (curriedTensor C) n).hom =
      (ρ_ K).inv⟦n⟧' := by
  ext i
  change (HomologicalComplex.rightUnitor' (K⟦n⟧)).inv i ≫ _ =
    (HomologicalComplex.rightUnitor' K).inv (i + n)
  rw [HomologicalComplex.rightUnitor'_inv, HomologicalComplex.rightUnitor'_inv]
  have h := ι_mapBifunctorShift₁Iso_hom_f K (𝟙_ (CochainComplex C ℤ)) (curriedTensor C) n i 0 i
    (add_zero i) (i + n) (i + n) rfl rfl
  erw [assoc, assoc, h]
  simp only [shiftFunctor_obj_X', curriedTensor_obj_obj, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_map_app, Iso.refl_inv, comp_id,
    Iso.cancel_iso_inv_left]
  erw [MonoidalCategory.id_whiskerRight, id_comp]
  rfl

lemma mapBifunctorShift₁Iso_hom_rightUnitor_hom :
    (mapBifunctorShift₁Iso K (𝟙_ (CochainComplex C ℤ)) (curriedTensor C) n).hom ≫
      (ρ_ K).hom⟦n⟧' = (ρ_ (K⟦n⟧)).hom := by
  rw [← cancel_epi (ρ_ (K⟦n⟧)).inv, reassoc_of% rightUnitor_inv_mapBifunctorShift₁Iso_hom,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Iso.inv_hom_id]

end CochainComplex

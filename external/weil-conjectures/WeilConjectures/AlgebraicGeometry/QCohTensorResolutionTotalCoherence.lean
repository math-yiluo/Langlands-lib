/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionTotalCoherence_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionTotalCoherence_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionTotalCoherence_localInst3 (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionTotalCoherence_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The componentwise identification of two successive chart restrictions. -/
noncomputable def tensorResolutionChartRestrictionComplexIso (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (E : CochainComplex Y.Modules ℤ) :
    ((Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE
      h).op))).mapHomologicalComplex
      (.up ℤ)).obj (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex
        (.up ℤ)).obj E) ≅
    ((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E :=
  (Functor.mapHomologicalComplexCompIso (tensorResolutionChartRestrictionIso Y V U h) (.up ℤ)).app E

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Inverse total tensor comparisons respect successive affine restrictions. -/
theorem tensorResolutionChartRestriction_total_inv (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (E F : CochainComplex Y.Modules ℤ) :
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let _RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let R := (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE
      h).op))).mapHomologicalComplex (.up ℤ)
    HomologicalComplex.mapBifunctorMap
        (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
        (tensorResolutionChartRestrictionComplexIso Y V U h F).hom
        (curriedTensor (Spec Γ(Y, V.1)).Modules) (.up ℤ) ≫
        (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).inv =
      (tensorResolutionRestrictionTotalIso (Spec.map (Y.presheaf.map (homOfLE h).op))
        (RU.obj E) (RU.obj F)).inv ≫
        R.map (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).inv ≫
        (tensorResolutionChartRestrictionComplexIso Y V U h
          (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules))).hom := by
  dsimp only
  ext i : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  rw [tensorResolution_ι_totalTensorMap_assoc,
    tensorResolution_ι_restrictionTotal_inv,
    tensorResolution_ι_restrictionTotal_inv_assoc]
  rw [Functor.mapHomologicalComplex_map_f]
  rw [← Functor.map_comp_assoc]
  rw [tensorResolution_ι_restrictionTotal_inv]
  simp only [Functor.map_comp, Category.assoc]
  change _ = _ ≫ _ ≫
    (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
        ((Scheme.Modules.restrictFunctor U.2.fromSpec).map
          (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i hpq)) ≫
      (tensorResolutionChartRestrictionIso Y V U h).hom.app _
  have hnat := (tensorResolutionChartRestrictionIso Y V U h).hom.naturality
    (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i hpq)
  simp only [Functor.comp_map] at hnat
  rw [hnat]
  change (((tensorResolutionChartRestrictionIso Y V U h).hom.app (E.X p)) ⊗ₘ
      ((tensorResolutionChartRestrictionIso Y V U h).hom.app (F.X q))) ≫
      (tensorResolutionRestrictionTensor V.2.fromSpec (E.X p) (F.X q)).inv ≫ _ = _
  rw [reassoc_of% tensorResolutionChartRestriction_tensor_inv]
  rfl

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Forward total tensor comparisons respect successive affine restrictions. -/
theorem tensorResolutionChartRestriction_total (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (E F : CochainComplex Y.Modules ℤ) :
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let R := (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE
      h).op))).mapHomologicalComplex (.up ℤ)
    R.map (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).hom ≫
        tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
          (RU.obj E) (RU.obj F) (RV.obj E) (RV.obj F)
          (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
          (tensorResolutionChartRestrictionComplexIso Y V U h F).hom =
      (tensorResolutionChartRestrictionComplexIso Y V U h
        (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules))).hom ≫
          (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).hom := by
  dsimp only [tensorResolutionRestrictionTensorMap]
  apply (cancel_mono (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [tensorResolutionChartRestriction_total_inv]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end AlgebraicGeometry

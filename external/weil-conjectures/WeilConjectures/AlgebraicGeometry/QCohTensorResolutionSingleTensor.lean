/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionSingleTensor_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionSingleTensor_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionSingleTensor_localInst3 (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionSingleTensor_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The inverse single-factor tensor comparison is the degree-(i,0) inclusion. -/
theorem tensorResolution_single₂_inv_f (X : Scheme.{u})
    (E : CochainComplex X.Modules ℤ) (N : X.Modules) (i : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor X.Modules) N E).inv.f i =
      (E.X i ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv) ≫
        HomologicalComplex.ιMapBifunctor E
          ((CochainComplex.singleFunctor X.Modules 0).obj N)
          (curriedTensor X.Modules) (.up ℤ) i 0 i (by simp) := by
  dsimp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_inv,
    HomologicalComplex.comp_f, Iso.symm_inv]
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  simp

end AlgebraicGeometry

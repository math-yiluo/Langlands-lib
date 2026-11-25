/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
noncomputable local instance trTotalSummandMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance trTotalSummandPreadditive
    (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance trTotalSummandZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trTotalSummandObjZero
    (X : Scheme.{u}) (E : X.Modules) :
    ((curriedTensor X.Modules).obj E).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf E

/-- Restriction of one summand of a total tensor map. -/
theorem tensorResolution_totalSummand_naturality {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (E F : CochainComplex Y.Modules ℤ)
    (E' F' : CochainComplex X.Modules ℤ)
    (a : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (b : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (p q i : ℤ) (h : p + q = i) :
    (Scheme.Modules.restrictFunctor j).map
        (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules)
          (.up ℤ) p q i h) ≫
      (tensorResolutionRestrictionTensorMap j E F E' F' a b).f i =
    (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).hom ≫
      (a.f p ⊗ₘ b.f q) ≫
      HomologicalComplex.ιMapBifunctor E' F' (curriedTensor X.Modules)
        (.up ℤ) p q i h := by
  dsimp only [tensorResolutionRestrictionTensorMap, HomologicalComplex.comp_f]
  rw [tensorResolution_map_ι_restrictionTotal_hom_assoc,
    tensorResolution_ι_totalTensorMap]

end AlgebraicGeometry

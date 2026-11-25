/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalSummandNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
noncomputable local instance trTotalPrecompMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trTotalPrecompZero (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trTotalPrecompObjZero (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

/-- Restriction of a total summand remains natural after precomposition. -/
theorem tensorResolution_totalSummand_naturality_precomp {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (E F : CochainComplex Y.Modules ℤ)
    (E' F' : CochainComplex X.Modules ℤ)
    (a : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (b : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (p q i : ℤ) (h : p + q = i)
    {W : X.Modules}
    (w : W ⟶ (Scheme.Modules.restrictFunctor j).obj (E.X p ⊗ F.X q)) :
    w ≫ (Scheme.Modules.restrictFunctor j).map
          (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules)
            (.up ℤ) p q i h) ≫
        (tensorResolutionRestrictionTensorMap j E F E' F' a b).f i =
      w ≫ (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).hom ≫
        (a.f p ⊗ₘ b.f q) ≫
        HomologicalComplex.ιMapBifunctor E' F' (curriedTensor X.Modules)
          (.up ℤ) p q i h := by
  rw [tensorResolution_totalSummand_naturality]

/-- The same square after two successive prefix maps. -/
theorem tensorResolution_totalSummand_naturality_twoPrecomp {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (E F : CochainComplex Y.Modules ℤ)
    (E' F' : CochainComplex X.Modules ℤ)
    (a : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (b : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F')
    (p q i : ℤ) (h : p + q = i)
    {W Z : X.Modules}
    (u : W ⟶ Z)
    (v : Z ⟶ (Scheme.Modules.restrictFunctor j).obj (E.X p ⊗ F.X q)) :
    u ≫ v ≫ (Scheme.Modules.restrictFunctor j).map
          (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules)
            (.up ℤ) p q i h) ≫
        (tensorResolutionRestrictionTensorMap j E F E' F' a b).f i =
      u ≫ v ≫ (tensorResolutionRestrictionTensor j (E.X p) (F.X q)).hom ≫
        (a.f p ⊗ₘ b.f q) ≫
        HomologicalComplex.ιMapBifunctor E' F' (curriedTensor X.Modules)
          (.up ℤ) p q i h := by
  rw [tensorResolution_totalSummand_naturality]

end AlgebraicGeometry

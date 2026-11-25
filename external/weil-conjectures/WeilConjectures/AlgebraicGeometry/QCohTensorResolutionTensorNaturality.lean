/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionHomologyZigzag

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionTensorNaturality_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionTensorNaturality_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionTensorNaturality_localInst3 (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionTensorNaturality_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Composition of total tensor maps. -/
theorem tensorResolution_totalTensor_comp {X : Scheme.{u}}
    {E₁ E₂ E₃ F₁ F₂ F₃ : CochainComplex X.Modules ℤ}
    (a : E₁ ⟶ E₂) (b : F₁ ⟶ F₂) (c : E₂ ⟶ E₃) (d : F₂ ⟶ F₃) :
    HomologicalComplex.mapBifunctorMap a b (curriedTensor X.Modules) (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap c d (curriedTensor X.Modules) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (a ≫ c) (b ≫ d)
        (curriedTensor X.Modules) (.up ℤ) := by
  ext i : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp [HomologicalComplex.ι_mapBifunctorMap, Category.assoc, whisker_exchange_assoc]

/-- A pair of chain squares induces a square on restricted total tensor complexes. -/
theorem tensorResolution_restrictedTensor_square {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    {E₁ E₂ F₁ F₂ : CochainComplex Y.Modules ℤ}
    {E₁' E₂' F₁' F₂' : CochainComplex X.Modules ℤ}
    (a : E₁ ⟶ E₂) (b : F₁ ⟶ F₂) (a' : E₁' ⟶ E₂') (b' : F₁' ⟶ F₂')
    (s₁ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E₁ ⟶ E₁')
    (s₂ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E₂ ⟶ E₂')
    (t₁ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F₁ ⟶ F₁')
    (t₂ : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F₂ ⟶ F₂')
    (ha : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map a ≫ s₂ = s₁ ≫ a')
    (hb : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map b ≫ t₂ = t₁ ≫ b') :
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a b (curriedTensor Y.Modules) (.up ℤ)) ≫
      (tensorResolutionRestrictionTotalIso j E₂ F₂).hom ≫
      HomologicalComplex.mapBifunctorMap s₂ t₂ (curriedTensor X.Modules) (.up ℤ) =
    (tensorResolutionRestrictionTotalIso j E₁ F₁).hom ≫
      HomologicalComplex.mapBifunctorMap s₁ t₁ (curriedTensor X.Modules) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap a' b' (curriedTensor X.Modules) (.up ℤ) := by
  have hn := HomologicalComplex.mapBifunctorComparison_naturality
    (tensorResolutionRestrictionTensorNatIso j).hom (.up ℤ) a b
  dsimp only [tensorResolutionRestrictionTotalIso, asIso_hom]
  rw [reassoc_of% hn, tensorResolution_totalTensor_comp,
    tensorResolution_totalTensor_comp, ha, hb]

end AlgebraicGeometry

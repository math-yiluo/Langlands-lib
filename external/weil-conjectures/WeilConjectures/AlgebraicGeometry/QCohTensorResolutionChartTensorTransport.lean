/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensorCompose

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartTransportMonoidal (X : Scheme.{u}) : MonoidalCategory
  X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trChartTransportZero (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartTransportObjZero (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Transport of the two factors of a chart tensor summand. -/
theorem tensorResolutionChartTensor_transport {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB)
    (b : NA ⟶ (ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).obj NB)
    (a : PA.complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj PB.complex)
    (hb : ∀ y, sB (b y) = N.val.map (homOfLE h).op (sA y)) (j : ℕ) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let EA := tensorResolutionChartComplex U MA PA
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    let i := -(j : ℤ)
    let fA := tilde.map (PA.complex.extendXIso ComplexShape.embeddingDownNat
      (i := j) (i' := i) rfl).inv
    let fB := tilde.map (PB.complex.extendXIso ComplexShape.embeddingDownNat
      (i := j) (i' := i) rfl).inv
    let gA := (tensorResolutionChartModel N U NA sA).hom ≫
      (Scheme.Modules.restrictFunctor U.2.fromSpec).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
    let gB := (tensorResolutionChartModel N V NB sB).hom ≫
      (Scheme.Modules.restrictFunctor V.2.fromSpec).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
    let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
      (PA.complex.extend ComplexShape.embeddingDownNat)
      (PB.complex.extend ComplexShape.embeddingDownNat)
      (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex PB.complex a)
    let χ := tensorResolutionChartRestrictionComplexIso Y V U h N0
    R.map (fA ⊗ₘ gA) ≫
        (tensorResolutionRestrictionTensor (Spec.map φ) (EA.X i) ((RU.obj N0).X 0)).hom ≫
          (a'.f i ⊗ₘ χ.hom.f 0) =
      (tensorResolutionRestrictionTensor (Spec.map φ) (tilde (PA.complex.X j)) (tilde NA)).hom ≫
        (tensorResolutionSemilinearMap φ (a.f j) ⊗ₘ tensorResolutionSemilinearMap φ b) ≫
          (fB ⊗ₘ gB) := by
  dsimp only
  let φ := Y.presheaf.map (homOfLE h).op
  let R := Scheme.Modules.restrictFunctor (Spec.map φ)
  let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
  let EA := tensorResolutionChartComplex U MA PA
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let i := -(j : ℤ)
  let fA := tilde.map (PA.complex.extendXIso ComplexShape.embeddingDownNat
    (i := j) (i' := i) rfl).inv
  let fB := tilde.map (PB.complex.extendXIso ComplexShape.embeddingDownNat
    (i := j) (i' := i) rfl).inv
  let gA := (tensorResolutionChartModel N U NA sA).hom ≫
    (Scheme.Modules.restrictFunctor U.2.fromSpec).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
  let gB := (tensorResolutionChartModel N V NB sB).hom ≫
    (Scheme.Modules.restrictFunctor V.2.fromSpec).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
  let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
    (PA.complex.extend ComplexShape.embeddingDownNat)
    (PB.complex.extend ComplexShape.embeddingDownNat)
    (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex PB.complex a)
  let χ := tensorResolutionChartRestrictionComplexIso Y V U h N0
  have hf : R.map fA ≫ a'.f i = tensorResolutionSemilinearMap φ (a.f j) ≫ fB :=
    tensorResolutionSemilinearComplexMap_extend_inv_f φ ComplexShape.embeddingDownNat
      PA.complex PB.complex a rfl
  have hg : R.map gA ≫ χ.hom.f 0 = tensorResolutionSemilinearMap φ b ≫ gB :=
    tensorResolutionChartCoefficient_naturality N V U h NA NB sA sB b hb
  exact tensorResolutionRestrictionTensor_comp_of (Spec.map φ) fA gA
    (a'.f i) (χ.hom.f 0) (tensorResolutionSemilinearMap φ (a.f j))
    (tensorResolutionSemilinearMap φ b) fB gB hf hg

end AlgebraicGeometry

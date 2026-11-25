/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartModel
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalSummandPrecomp

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartSummandMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trChartSummandZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartSummandObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The chart summand inclusion commutes with restriction after the component
transport maps have been precomposed. -/
theorem tensorResolutionChartSummand_naturality {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (_sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB)
    (a : PA.complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj PB.complex)
    (j : ℕ) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let EA := tensorResolutionChartComplex U MA PA
    let EB := tensorResolutionChartComplex V MB PB
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
      (PA.complex.extend ComplexShape.embeddingDownNat)
      (PB.complex.extend ComplexShape.embeddingDownNat)
      (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex PB.complex a)
    let χ := tensorResolutionChartRestrictionComplexIso Y V U h N0
    let i := -(j : ℤ)
    let fA := tilde.map
      (PA.complex.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv
    let gA := (tensorResolutionChartModel N U NA sA).hom ≫
      (Scheme.Modules.restrictFunctor U.2.fromSpec).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
    R.map (tensorResolutionTildeTensorHom _ (PA.complex.X j) NA) ≫
      R.map (fA ⊗ₘ gA) ≫
        R.map (HomologicalComplex.ιMapBifunctor EA (RU.obj N0) (curriedTensor _)
          (.up ℤ) i 0 i (by simp)) ≫
        (tensorResolutionRestrictionTensorMap (Spec.map φ)
          EA (RU.obj N0) EB (RV.obj N0) a' χ.hom).f i =
      R.map (tensorResolutionTildeTensorHom _ (PA.complex.X j) NA) ≫
        R.map (fA ⊗ₘ gA) ≫
          (tensorResolutionRestrictionTensor (Spec.map φ)
            (EA.X i) ((RU.obj N0).X 0)).hom ≫
          (a'.f i ⊗ₘ χ.hom.f 0) ≫
          HomologicalComplex.ιMapBifunctor EB (RV.obj N0) (curriedTensor _)
            (.up ℤ) i 0 i (by simp) := by
  dsimp only
  exact tensorResolution_totalSummand_naturality_twoPrecomp
    (Spec.map (Y.presheaf.map (homOfLE h).op))
    (tensorResolutionChartComplex U MA PA)
    (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor Y.Modules 0).obj N))
    (tensorResolutionChartComplex V MB PB)
    (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor Y.Modules 0).obj N))
    (tensorResolutionSemilinearComplexMap (Y.presheaf.map (homOfLE h).op) (.up ℤ)
      (PA.complex.extend ComplexShape.embeddingDownNat)
      (PB.complex.extend ComplexShape.embeddingDownNat)
      (tensorResolutionExtendSemilinear (Y.presheaf.map (homOfLE h).op).hom
        ComplexShape.embeddingDownNat PA.complex PB.complex a))
    (tensorResolutionChartRestrictionComplexIso Y V U h
      ((CochainComplex.singleFunctor Y.Modules 0).obj N)).hom
    (-(j : ℤ)) 0 (-(j : ℤ)) (by simp)
    ((Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
      (tensorResolutionTildeTensorHom _ (PA.complex.X j) NA))
    ((Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
      ((tilde.map (PA.complex.extendXIso ComplexShape.embeddingDownNat
        (i := j) (i' := -(j : ℤ)) rfl).inv) ⊗ₘ
      ((tensorResolutionChartModel N U NA sA).hom ≫
        (Scheme.Modules.restrictFunctor U.2.fromSpec).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)))

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComponents
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensorCompose
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalSummandNaturality
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorTransport
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalSummandPrecomp
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionThreeSquares
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartSummandNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartTensorNaturalMonoidal (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance trChartTensorNaturalPreadditive (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance trChartTensorNaturalZero (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartTensorNaturalObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Naturality of the chart tensor inclusion after transport to nonzero degrees. -/
theorem tensorResolutionChartTensorIso_naturality_positive_core {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let _RC := R.mapHomologicalComplex (.up ℤ)
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
    let LB := ((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex
    let EA := tensorResolutionChartComplex U MA PA
    let EB := tensorResolutionChartComplex V MB PB
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    ∀ (b : NA ⟶ (ModuleCat.restrictScalars φ.hom).obj NB)
      (a : PA.complex ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.down
        ℕ)).obj PB.complex)
      (k : LA ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.down ℕ)).obj LB),
      (∀ y, sB (b y) = N.val.map (homOfLE h).op (sA y)) →
      (∀ (j : ℕ) (x : PA.complex.X j) (y : NA),
        k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
          (show PB.complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (show NB from b y)) →
      let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
        (PA.complex.extend ComplexShape.embeddingDownNat) (PB.complex.extend
          ComplexShape.embeddingDownNat)
        (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex
          PB.complex a)
      let _k' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
        (LA.extend ComplexShape.embeddingDownNat) (LB.extend ComplexShape.embeddingDownNat)
        (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k)
      ∀ j : ℕ,
      let i := -(j : ℤ)
      let fA := tilde.map
        (PA.complex.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv
      let fB := tilde.map
        (PB.complex.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv
      let gA := (tensorResolutionChartModel N U NA sA).hom ≫
        (Scheme.Modules.restrictFunctor U.2.fromSpec).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
      let gB := (tensorResolutionChartModel N V NB sB).hom ≫
        (Scheme.Modules.restrictFunctor V.2.fromSpec).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
      R.map (tensorResolutionTildeTensorHom _ (PA.complex.X j) NA) ≫
        R.map (fA ⊗ₘ gA) ≫
          R.map (HomologicalComplex.ιMapBifunctor EA (RU.obj N0) (curriedTensor _)
            (.up ℤ) i 0 i (by simp)) ≫
          (tensorResolutionRestrictionTensorMap (Spec.map φ)
            EA (RU.obj N0) EB (RV.obj N0) a'
            (tensorResolutionChartRestrictionComplexIso Y V U h N0).hom).f i =
        tensorResolutionSemilinearMap φ (k.f j) ≫
          tensorResolutionTildeTensorHom _ (PB.complex.X j) NB ≫
          (fB ⊗ₘ gB) ≫
          HomologicalComplex.ιMapBifunctor EB (RV.obj N0) (curriedTensor _)
            (.up ℤ) i 0 i (by simp) := by
  dsimp only
  intro b a k hb hk j
  let φ := Y.presheaf.map (homOfLE h).op
  let R := Scheme.Modules.restrictFunctor (Spec.map φ)
  let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
  let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
  let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
  let LB := ((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex
  let EA := tensorResolutionChartComplex U MA PA
  let EB := tensorResolutionChartComplex V MB PB
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
    (PA.complex.extend ComplexShape.embeddingDownNat) (PB.complex.extend
      ComplexShape.embeddingDownNat)
    (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex PB.complex a)
  let k' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
    (LA.extend ComplexShape.embeddingDownNat) (LB.extend ComplexShape.embeddingDownNat)
    (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k)
  let χ := tensorResolutionChartRestrictionComplexIso Y V U h N0
  let i := -(j : ℤ)
  · let fA := tilde.map (PA.complex.extendXIso ComplexShape.embeddingDownNat (i := j) (i' :=
    i) rfl).inv
    let fB := tilde.map (PB.complex.extendXIso ComplexShape.embeddingDownNat (i := j) (i' :=
      i) rfl).inv
    let gA := (tensorResolutionChartModel N U NA sA).hom ≫
      (Scheme.Modules.restrictFunctor U.2.fromSpec).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
    let gB := (tensorResolutionChartModel N V NB sB).hom ≫
      (Scheme.Modules.restrictFunctor V.2.fromSpec).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv
    have hp : R.map (fA ⊗ₘ gA) ≫
        (tensorResolutionRestrictionTensor (Spec.map φ) (EA.X i) ((RU.obj N0).X 0)).hom ≫
          (a'.f i ⊗ₘ χ.hom.f 0) =
        (tensorResolutionRestrictionTensor (Spec.map φ) (tilde (PA.complex.X j)) (tilde NA)).hom ≫
          (tensorResolutionSemilinearMap φ (a.f j) ⊗ₘ tensorResolutionSemilinearMap φ b) ≫
          (fB ⊗ₘ gB) := by
      exact tensorResolutionChartTensor_transport N V U h MA NA MB NB sA sB
        PA PB b a hb j
    have hι := tensorResolutionChartSummand_naturality
      N V U h MA NA MB NB sA sB PA PB a j
    have ht := tensorResolutionSemilinearMap_tensor φ
      (PA.complex.X j) NA (PB.complex.X j) NB (a.f j) b (k.f j) (hk j)
    rw [hι]
    rw [reassoc_of% hp]
    rw [reassoc_of% ht]
end AlgebraicGeometry

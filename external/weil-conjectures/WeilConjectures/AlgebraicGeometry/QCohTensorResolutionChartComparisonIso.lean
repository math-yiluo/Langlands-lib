/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartModel
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparison
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionKFlatBundledRing

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Compare the chart resolution with a fixed global K-flat resolution after restriction. -/
noncomputable def tensorResolutionChartComparisonIso
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i ≅
    (CochainComplex.mapBifunctor
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i := by
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RC := R.mapHomologicalComplex (.up ℤ)
  let E := tensorResolutionChartComplex U MA P
  let M0 := (CochainComplex.singleFunctor Y.Modules 0).obj M
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let r := tensorResolutionChartAugmentation M U MA sM P
  have hE : CochainComplex.IsKFlatTensor (R := (Spec Γ(Y, U.1)).sheaf) E :=
    tensorResolution_isKFlat_bundledRing Γ(Y, U.1) MA P
  have hK' := isKFlat_restrict U.2.fromSpec K hK
  have hF' := isKFlat_restrict U.2.fromSpec F hF
  have : QuasiIso q := hq
  have : QuasiIso s := hs
  have hq' : QuasiIso (RC.map q) := by dsimp [RC, R]; infer_instance
  have hs' : QuasiIso (RC.map s) := by dsimp [RC, R]; infer_instance
  exact tensorResolutionComparison (Spec Γ(Y, U.1)).sheaf E (RC.obj K) (RC.obj M0)
    (RC.obj F) (RC.obj N0) r (RC.map q) (RC.map s) hE hK' hF'
    (tensorResolutionChartAugmentation_quasiIso M U MA sM P) hq' hs' i

end AlgebraicGeometry

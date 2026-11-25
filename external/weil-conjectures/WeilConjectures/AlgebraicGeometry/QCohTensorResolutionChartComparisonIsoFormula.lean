/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso

/-! # Defining formula for the single-chart K-flat comparison

Source: Stacks Project, Tags 06YT and 08DX(2).
-/

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

-- The concrete chart construction has large homology types.
/-- The concrete chart comparison has its specified common-resolution hom.

Source: Stacks Tags 06YT and 08DX(2), the specified common K-flat comparison.
Proof in words: unfold tensorResolutionChartComparisonIso, keeping the section
ring bundled. Its restriction functor, extended sheafified projective resolution,
augmentation and restricted q and s are the local terms displayed here. The two
K-flatness proofs and the quasi-isomorphism proofs coincide by proof irrelevance.
Project the hom of the resulting isomorphism. The two sides are the same
four-map tensorResolutionComparison construction. This is a single-chart
identification; it asserts no naturality under a change of chart.

(blueprint: new-h4-qcoh-chart-comparison-hom-identification) -/
theorem tensorResolutionChartComparisonIso_hom_eq
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RC := R.mapHomologicalComplex (.up ℤ)
  let E := tensorResolutionChartComplex U MA P
  let M0 := (CochainComplex.singleFunctor Y.Modules 0).obj M
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let r := tensorResolutionChartAugmentation M U MA sM P
  let hE : CochainComplex.IsKFlatTensor (R := (Spec Γ(Y, U.1)).sheaf) E :=
    tensorResolution_isKFlat_bundledRing Γ(Y, U.1) MA P
  let hK' := isKFlat_restrict U.2.fromSpec K hK
  let hF' := isKFlat_restrict U.2.fromSpec F hF
  letI : QuasiIso q := hq
  letI : QuasiIso s := hs
  let hq' : QuasiIso (RC.map q) := by dsimp [RC, R]; infer_instance
  let hs' : QuasiIso (RC.map s) := by dsimp [RC, R]; infer_instance
  (tensorResolutionChartComparisonIso Y M N U MA sM P K F q s hK hF hq hs i).hom =
  (tensorResolutionComparison (Spec Γ(Y, U.1)).sheaf E (RC.obj K) (RC.obj M0)
    (RC.obj F) (RC.obj N0) r (RC.map q) (RC.map s) hE hK' hF'
    (tensorResolutionChartAugmentation_quasiIso M U MA sM P) hq' hs' i).hom := by
  rfl

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateSheafIso

/-! # Factorization of canonical affine tensor coordinates

Source: the definition of tensorResolutionCoordinateSheafIso, following Stacks Tag 08DX(2).
(blueprint: new-t3-qcoh-tensor-resolution-coordinate-factorization).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
noncomputable local instance QCohTensorResolutionCoordinateFactorization_monoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance QCohTensorResolutionCoordinateFactorization_zero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance QCohTensorResolutionCoordinateFactorization_objZero
    (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The canonical sheaf coordinates factor through the affine model and K-flat comparison.

Source: the definition of tensorResolutionCoordinateSheafIso. The proof unfolds
that definition once; exposing its formula avoids repeated expensive unfolding
in proofs about the comparison.

(blueprint: new-t3-qcoh-tensor-resolution-coordinate-factorization) -/
theorem tensorResolutionCoordinateSheafIso_factors
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ) :
    tensorResolutionCoordinateSheafIso Y M N U MA NA sM sN P K F q s hK hF hq hs n =
      (tensorResolutionChartHomologyIso N U MA NA sN P n ≪≫
        tensorResolutionChartComparisonIso Y M N U MA sM P K F q s hK hF hq hs (-(n : ℤ)) ≪≫
        (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K
          ((CochainComplex.singleFunctor Y.Modules 0).obj N) (-(n : ℤ))).symm) := by
  rfl
end AlgebraicGeometry

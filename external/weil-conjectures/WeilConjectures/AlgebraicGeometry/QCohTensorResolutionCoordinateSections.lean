/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateSheafIso
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonIsoFormula

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The canonical affine section coordinates induced by the sheaf comparison. -/
noncomputable def tensorResolutionCoordinateSections
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
    ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≃ₗ[Γ(Y, U.1)]
    ((CochainComplex.mapBifunctor K
      ((CochainComplex.singleFunctor Y.Modules 0).obj N) (curriedTensor Y.Modules)).homology
        (-(n : ℤ))).val.obj (op U.1) :=
  (tilde.isoTop (R := .of (Γ(Y, U.1) : Type u)) _ ≪≫
    (moduleSpecΓFunctor (R := .of (Γ(Y, U.1) : Type u))).mapIso
      (tensorResolutionCoordinateSheafIso Y M N U MA NA sM sN P K F q s hK hF hq hs n)
  ).toLinearEquiv.trans
    (Scheme.Modules.sectionsRestrictFromSpecLinearEquiv _ U.2)

end AlgebraicGeometry

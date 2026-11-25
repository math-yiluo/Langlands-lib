/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionAffineModel
public import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

noncomputable local instance chartMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

noncomputable local instance chartPreadditive (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some

local instance chartTensorZero (X : Scheme.{u}) :
    (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf

local instance chartTensorObjZero (X : Scheme.{u}) (F : X.Modules) :
    ((curriedTensor X.Modules).obj F).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf F

/-- The affine model specified by a choice of coordinates on sections. -/
noncomputable def tensorResolutionChartModel {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsQuasicoherent] (U : Y.affineOpens)
    (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (s : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1)) :
    tilde (R := .of (Γ(Y, U.1) : Type u)) MA ≅ M.restrict U.2.fromSpec := by
  let e := s.trans (Scheme.Modules.sectionsRestrictFromSpecLinearEquiv M U.2).symm
  have : IsIso (M.restrict U.2.fromSpec).fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  exact (tilde.functor (.of (Γ(Y, U.1) : Type u))).mapIso e.toModuleIso ≪≫
    asIso (M.restrict U.2.fromSpec).fromTildeΓ

-- Tensor-coordinate comparisons require substantial definitional reduction.
/-- Exact open restriction commutes with ordinary tensor homology. -/
noncomputable def tensorResolutionRestrictHomologyIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (K : CochainComplex Y.Modules ℤ)
    (N : Y.Modules) (i : ℤ) :
    (Scheme.Modules.restrictFunctor j).obj
      ((CochainComplex.mapBifunctor K
        ((CochainComplex.singleFunctor Y.Modules 0).obj N) (curriedTensor _)).homology i) ≅
    (CochainComplex.mapBifunctor
      (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K)
      ((CochainComplex.singleFunctor X.Modules 0).obj (N.restrict j))
      (curriedTensor _)).homology i := by
  let R := Scheme.Modules.restrictFunctor j
  let RC := R.mapHomologicalComplex (.up ℤ)
  letI : (Scheme.Modules.pullback j).Monoidal := Scheme.Modules.pullbackMonoidal j
  letI : R.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback j).symm
  let B := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let E := CochainComplex.mapBifunctor K B (curriedTensor Y.Modules)
  let c := asIso (HomologicalComplex.mapBifunctorComparison
    (Functor.OplaxMonoidal.δNatTrans R) (.up ℤ) K B)
  let s := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app N
  let t := ((curriedTensor X.Modules).map₂CochainComplex.obj (RC.obj K)).mapIso s
  exact ((E.sc i).mapHomologyIso R).symm ≪≫
    (HomologicalComplex.homologyFunctor X.Modules (.up ℤ) i).mapIso (c ≪≫ t)

-- Tensor-coordinate comparisons require substantial definitional reduction.
/-- Ordinary tensor-resolution homology has the asserted coordinates on each affine chart. -/
theorem exists_tensorResolutionChartCoordinates
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U, ProjectiveResolution (MA U))
    (K : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K) (hq : QuasiIso q) (n : ℕ) :
    ∀ U : Y.affineOpens, Nonempty (
      ((((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj
        (P U).complex).homology n) ≃ₗ[Γ(Y, U.1)]
      (CochainComplex.mapBifunctor K
        ((CochainComplex.singleFunctor Y.Modules 0).obj N)
        (curriedTensor _)).homology (-(n : ℤ)) |>.val.obj (op U.1)) := by
  classical
  intro U
  let A := (Γ(Y, U.1) : Type u)
  let X := Spec (.of A)
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RC := R.mapHomologicalComplex (.up ℤ)
  let S := CochainComplex.singleFunctor X.Modules 0
  let eM := tensorResolutionChartModel M U (MA U) (sM U)
  let eN := tensorResolutionChartModel N U (NA U) (sN U)
  let qU := RC.map q ≫
    ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app M).hom ≫
      S.map eM.inv
  have : QuasiIso q := hq
  have hqU : QuasiIso qU := by dsimp [qU]; infer_instance
  obtain ⟨e⟩ := exists_tensorResolutionSections A (MA U) (NA U) (P U)
    (RC.obj K) qU (isKFlat_restrict U.2.fromSpec K hK) hqU n
  let T := (curriedTensor X.Modules).map₂CochainComplex.obj (RC.obj K)
  let H := HomologicalComplex.homologyFunctor X.Modules (.up ℤ) (-(n : ℤ))
  let h := H.mapIso (T.mapIso (S.mapIso eN)) ≪≫
    (tensorResolutionRestrictHomologyIso U.2.fromSpec K N (-(n : ℤ))).symm
  let Γ := moduleSpecΓFunctor (R := .of A)
  exact ⟨e.trans ((Γ.mapIso h).toLinearEquiv.trans
    (Scheme.Modules.sectionsRestrictFromSpecLinearEquiv _ U.2))⟩

end AlgebraicGeometry

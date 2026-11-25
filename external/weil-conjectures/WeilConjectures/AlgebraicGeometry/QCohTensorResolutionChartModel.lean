/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartRestriction
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionExtendHomology
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSingleTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionChartModel_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionChartModel_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionChartModel_localInst3 (X : Scheme.{u}) : (curriedTensor
  X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionChartModel_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The sheafified nonpositive resolution on a specified affine chart. -/
noncomputable abbrev tensorResolutionChartComplex {Y : Scheme.{u}}
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (P : ProjectiveResolution MA) : CochainComplex (Spec Γ(Y, U.1)).Modules ℤ :=
  ((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
    (P.complex.extend ComplexShape.embeddingDownNat)

/-- The augmentation to the literal restriction of the coefficient complex. -/
noncomputable def tensorResolutionChartAugmentation {Y : Scheme.{u}}
    (M : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1)) (P : ProjectiveResolution MA) :
    tensorResolutionChartComplex U MA P ⟶
      ((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj M) :=
  tensorResolutionTildeAugmentation _ MA P ≫
    (CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
      (tensorResolutionChartModel M U MA sM).hom ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app M).inv

instance tensorResolutionChartAugmentation_quasiIso {Y : Scheme.{u}}
    (M : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1)) (P : ProjectiveResolution MA) :
    QuasiIso (tensorResolutionChartAugmentation M U MA sM P) := by
  let f := tensorResolutionTildeAugmentation (Γ(Y, U.1) : Type u) MA P
  let g := (CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
    (tensorResolutionChartModel M U MA sM).hom
  let t := ((HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app M).inv
  have : QuasiIso f := tensorResolutionTildeAugmentation_quasiIso _ MA P
  have : IsIso g := by dsimp [g]; infer_instance
  have : IsIso t := by dsimp [t]; infer_instance
  change QuasiIso (f ≫ g ≫ t)
  infer_instance

/-- The affine tensor model, with target the literal restricted second coefficient. -/
noncomputable def tensorResolutionChartTensorIso {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1)) (P : ProjectiveResolution MA) :
    ((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
        ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).extend
          ComplexShape.embeddingDownNat) ≅
      CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Y.Modules 0).obj N))
        (curriedTensor (Spec Γ(Y, U.1)).Modules) := by
  let A := (Γ(Y, U.1) : Type u)
  let X := Spec Γ(Y, U.1)
  let E := P.complex.extend ComplexShape.embeddingDownNat
  let T := tilde.functor Γ(Y, U.1)
  letI : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let TC := T.mapHomologicalComplex (.up ℤ)
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let S := CochainComplex.singleFunctor X.Modules 0
  let c := tensorResolutionMapExtendIso (tensorRight NA)
    ComplexShape.embeddingDownNat P.complex
  let d := (Functor.mapHomologicalComplexCompIso
    (tensorResolutionTildeTensorRightIso A NA) (.up ℤ)).app E
  let t := (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor X.Modules)
    (tilde (R := Γ(Y, U.1)) NA) (TC.obj E)).symm
  let eN := S.mapIso (tensorResolutionChartModel N U NA sN) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app N).symm
  exact TC.mapIso c.symm ≪≫ d ≪≫ t ≪≫
    ((curriedTensor X.Modules).map₂CochainComplex.obj (TC.obj E)).mapIso eN

/-- Ordinary resolution homology in its normalized affine tensor model. -/
noncomputable def tensorResolutionChartHomologyIso {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1)) (P : ProjectiveResolution MA) (n : ℕ) :
    tilde (R := Γ(Y, U.1))
        ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≅
      (CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Y.Modules 0).obj N))
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology (-(n : ℤ)) := by
  let T := tilde.functor Γ(Y, U.1)
  letI : T.PreservesHomology := tilde_preservesHomology (Γ(Y, U.1) : Type u)
  let L := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex
  let h := tensorResolutionExtendLeftHomologyData ComplexShape.embeddingDownNat
    L (i := n) (i' := -(n : ℤ)) rfl (L.sc n).homologyData.left
  exact (h.map T).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor (Spec Γ(Y, U.1)).Modules (.up ℤ) (-(n : ℤ))).mapIso
      (tensorResolutionChartTensorIso N U MA NA sN P)

end AlgebraicGeometry

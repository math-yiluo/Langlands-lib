/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateSections
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateFactorization
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSectionNaturality
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

-- The canonical coordinate comparison combines three homology squares.
/-- The canonical chart coordinates commute with augmented semilinear tensor comparisons.

Source: Stacks Tags 08DX(2), 08DV, 06YT and 01I9.

Proof in words: the affine tensor-homology square uses hb and hk. The common
K-flat comparison square uses ha and naturality of open restriction. Compose
them by functoriality and associativity. The factorization formula identifies
their composite with the canonical coordinate sheaf isomorphism. Apply the
naturality of the affine sections unit, in tensorResolutionSection_naturality,
to obtain the displayed equality of sections.

(blueprint: new-g2-existing-qcoh-tensor-resolution-coordinate-naturality) -/
theorem tensorResolutionCoordinateSections_naturality
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U, ProjectiveResolution (MA U))
    (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ)
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (b : NA U →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom] NA V)
    (a : (P U).complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj
        (P V).complex)
    (k : ((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj (P U).complex ⟶
      ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex
        (.down ℕ)).obj
        (((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj (P V).complex))
    (ha : ∀ x : (P U).complex.X 0,
      sM V ((P V).π.f 0 (a.f 0 x)) =
        M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x)))
    (hb : ∀ y : NA U,
      sN V (b y) = N.val.map (homOfLE h).op (sN U y))
    (hk : ∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
      k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
        (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let Q := (CochainComplex.mapBifunctor K
      ((CochainComplex.singleFunctor Y.Modules 0).obj N)
      (curriedTensor Y.Modules)).homology (-(n : ℤ))
    let e := (((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj
      (P V).complex).sc n |>.mapHomologyIso
        (ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom)
    ∀ x, Q.val.map (homOfLE h).op
        (tensorResolutionCoordinateSections Y M N U (MA U) (NA U)
          (sM U) (sN U) (P U) K F q s hK hF hq hs n x) =
      tensorResolutionCoordinateSections Y M N V (MA V) (NA V)
        (sM V) (sN V) (P V) K F q s hK hF hq hs n
        (e.hom (HomologicalComplex.homologyMap k n x)) := by
  dsimp only
  let φ := Y.presheaf.map (homOfLE h).op
  let R := Scheme.Modules.restrictFunctor (Spec.map φ)
  let LA := ((tensorRight (NA U)).mapHomologicalComplex (.down ℕ)).obj (P U).complex
  let LB := ((tensorRight (NA V)).mapHomologicalComplex (.down ℕ)).obj (P V).complex
  let Q := (CochainComplex.mapBifunctor K
    ((CochainComplex.singleFunctor Y.Modules 0).obj N)
    (curriedTensor Y.Modules)).homology (-(n : ℤ))
  let dA := tensorResolutionCoordinateSheafIso Y M N U (MA U) (NA U)
    (sM U) (sN U) (P U) K F q s hK hF hq hs n
  let dB := tensorResolutionCoordinateSheafIso Y M N V (MA V) (NA V)
    (sM V) (sN V) (P V) K F q s hK hF hq hs n
  let t := HomologicalComplex.homologyMap k n ≫
    ((LB.sc n).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom
  let fA := tensorResolutionChartHomologyIso N U (MA U) (NA U) (sN U) (P U) n
  let fB := tensorResolutionChartHomologyIso N V (MA V) (NA V) (sN V) (P V) n
  let gA := tensorResolutionChartComparisonIso Y M N U (MA U) (sM U) (P U)
    K F q s hK hF hq hs (-(n : ℤ)) ≪≫
      (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K
        ((CochainComplex.singleFunctor Y.Modules 0).obj N) (-(n : ℤ))).symm
  let gB := tensorResolutionChartComparisonIso Y M N V (MA V) (sM V) (P V)
    K F q s hK hF hq hs (-(n : ℤ)) ≪≫
      (tensorResolutionNormalizedRestrictHomologyIso V.2.fromSpec K
        ((CochainComplex.singleFunctor Y.Modules 0).obj N) (-(n : ℤ))).symm
  have hf := tensorResolutionChartHomologyIso_naturality Y N MA NA sN P n V U h
    b a k hb hk
  have hg := tensorResolutionChartComparisonIso_naturality Y M N MA sM P
    K F q s hK hF hq hs n V U h a ha
  have hc : R.map (fA ≪≫ gA).hom ≫
      (tensorResolutionChartRestrictionIso Y V U h).hom.app Q =
      tensorResolutionSemilinearMap φ t ≫ (fB ≪≫ gB).hom := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [hg]
    erw [reassoc_of% hf]
  have hd : R.map dA.hom ≫ (tensorResolutionChartRestrictionIso Y V U h).hom.app Q =
      tensorResolutionSemilinearMap φ t ≫ dB.hom := by
    have edA : dA = fA ≪≫ gA :=
      tensorResolutionCoordinateSheafIso_factors Y M N U (MA U) (NA U)
        (sM U) (sN U) (P U) K F q s hK hF hq hs n
    have edB : dB = fB ≪≫ gB :=
      tensorResolutionCoordinateSheafIso_factors Y M N V (MA V) (NA V)
        (sM V) (sN V) (P V) K F q s hK hF hq hs n
    rw [edA, edB]
    exact hc
  intro x
  exact tensorResolutionSection_naturality Y Q V U h
    (LA.homology n) (LB.homology n) dA dB t hd x

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionPositiveTail

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartTensorSquareMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trChartTensorSquareZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartTensorSquareObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The chart tensor comparison is natural for the supplied pure-tensor maps. -/
theorem tensorResolutionChartTensorIso_naturality_of_pure_tensors {Y : Scheme.{u}}
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
    (k : ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex ⟶
      ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex
        (.down ℕ)).obj (((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex))
    (hb : ∀ y, sB (b y) = N.val.map (homOfLE h).op (sA y))
    (hk : ∀ (j : ℕ) (x : PA.complex.X j) (y : NA),
      k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
        (show PB.complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (show NB from b y)) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let RC := R.mapHomologicalComplex (.up ℤ)
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
    let LB := ((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex
    let EA := tensorResolutionChartComplex U MA PA
    let EB := tensorResolutionChartComplex V MB PB
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    let a' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
      (PA.complex.extend ComplexShape.embeddingDownNat)
      (PB.complex.extend ComplexShape.embeddingDownNat)
      (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat PA.complex PB.complex a)
    let k' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
      (LA.extend ComplexShape.embeddingDownNat) (LB.extend ComplexShape.embeddingDownNat)
      (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k)
    RC.map (tensorResolutionChartTensorIso N U MA NA sA PA).hom ≫
      tensorResolutionRestrictionTensorMap (Spec.map φ) EA (RU.obj N0) EB (RV.obj N0)
        a' (tensorResolutionChartRestrictionComplexIso Y V U h N0).hom =
      k' ≫ (tensorResolutionChartTensorIso N V MB NB sB PB).hom := by
  dsimp only
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i ≤ 0
  · let j : ℕ := Int.toNat (-i)
    have hji : -(j : ℤ) = i := by dsimp [j]; omega
    rw [← hji]
    exact tensorResolutionChartTensorIso_naturality_positive
      N V U h MA NA MB NB sA sB PA PB b a k hb hk j
  · have hpos : 0 < i := by omega
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
    have hzero := tensorResolution_extended_two_functors_isZero
      (tilde.functor Γ(Y, U.1)) R LA i hpos
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    exact hzero.eq_of_src _ _

end AlgebraicGeometry

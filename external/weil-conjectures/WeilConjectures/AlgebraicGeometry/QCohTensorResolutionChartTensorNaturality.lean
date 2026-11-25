/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorComponents

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartTensorPositiveMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trChartTensorPositiveZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartTensorPositiveObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- The supplied pure-tensor formula gives each nonzero chart tensor component. -/
theorem tensorResolutionChartTensorIso_naturality_positive {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB) :
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
      let k' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
        (LA.extend ComplexShape.embeddingDownNat) (LB.extend ComplexShape.embeddingDownNat)
        (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k)
      ∀ j : ℕ,
      (RC.map (tensorResolutionChartTensorIso N U MA NA sA PA).hom ≫
          tensorResolutionRestrictionTensorMap (Spec.map φ) EA (RU.obj N0) EB (RV.obj N0)
            a' (tensorResolutionChartRestrictionComplexIso Y V U h N0).hom).f (-(j : ℤ)) =
        (k' ≫ (tensorResolutionChartTensorIso N V MB NB sB PB).hom).f (-(j : ℤ)) := by
  dsimp only
  intro b a k hb hk j
  let φ := Y.presheaf.map (homOfLE h).op
  let R := Scheme.Modules.restrictFunctor (Spec.map φ)
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
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    have : IsIso (R.map (tilde.map (LA.extendXIso ComplexShape.embeddingDownNat
        (i := j) (i' := i) rfl).inv)) := by
      change IsIso (R.map ((tilde.functor Γ(Y, U.1)).map
        (LA.extendXIso ComplexShape.embeddingDownNat (i := j) (i' := i) rfl).inv))
      infer_instance
    apply (cancel_epi (R.map (tilde.map (LA.extendXIso ComplexShape.embeddingDownNat
      (i := j) (i' := i) rfl).inv))).1
    rw [← Functor.map_comp_assoc, tensorResolutionChartTensorIso_f N U MA NA sA PA j]
    simp only [Functor.map_comp, Category.assoc]
    have hk' := tensorResolutionSemilinearComplexMap_extend_inv_f φ
      ComplexShape.embeddingDownNat LA LB k (i := j) (i' := i) rfl
    change R.map (tilde.map (LA.extendXIso ComplexShape.embeddingDownNat
        (i := j) (i' := i) rfl).inv) ≫ k'.f i =
      tensorResolutionSemilinearMap φ (k.f j) ≫
        tilde.map (LB.extendXIso ComplexShape.embeddingDownNat
          (i := j) (i' := i) rfl).inv at hk'
    rw [reassoc_of% hk']
    rw [tensorResolutionChartTensorIso_f N V MB NB sB PB j]
    exact tensorResolutionChartTensorIso_naturality_positive_core
      N V U h MA NA MB NB sA sB PA PB b a k hb hk j

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyFromSquare

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartHomFromSquareMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trChartHomFromSquareZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartHomFromSquareObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Naturality of chart homology follows from the tensor-model chain square. -/
theorem tensorResolutionChartHomologyIso_naturality_of_square
    (Y : Scheme.{u}) (N : Y.Modules) [N.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB)
    (n : ℕ) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let RC := R.mapHomologicalComplex (.up ℤ)
    let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
    let LB := ((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex
    let EA := tensorResolutionChartComplex U MA PA
    let EB := tensorResolutionChartComplex V MB PB
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    ∀ (k : LA ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.down ℕ)).obj LB)
      (l : RC.obj (CochainComplex.mapBifunctor EA (RU.obj N0)
        (curriedTensor (Spec Γ(Y, U.1)).Modules)) ⟶
        CochainComplex.mapBifunctor EB (RV.obj N0)
          (curriedTensor (Spec Γ(Y, V.1)).Modules)),
      (let k' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
          (LA.extend ComplexShape.embeddingDownNat)
          (LB.extend ComplexShape.embeddingDownNat)
          (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k)
       RC.map (tensorResolutionChartTensorIso N U MA NA sA PA).hom ≫ l =
         k' ≫ (tensorResolutionChartTensorIso N V MB NB sB PB).hom) →
      let t := HomologicalComplex.homologyMap k n ≫
        ((LB.sc n).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom
      R.map (tensorResolutionChartHomologyIso N U MA NA sA PA n).hom ≫
          (((CochainComplex.mapBifunctor EA (RU.obj N0)
            (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc (-(n : ℤ))).mapHomologyIso R).inv ≫
          HomologicalComplex.homologyMap l (-(n : ℤ)) =
        tensorResolutionSemilinearMap φ t ≫
          (tensorResolutionChartHomologyIso N V MB NB sB PB n).hom := by
  dsimp only
  intro k l hl
  let : (tilde.functor Γ(Y, U.1)).PreservesHomology :=
    tilde_preservesHomology (Γ(Y, U.1) : Type u)
  let : (tilde.functor Γ(Y, V.1)).PreservesHomology :=
    tilde_preservesHomology (Γ(Y, V.1) : Type u)
  rw [tensorResolutionChartHomologyIso_hom N U MA NA sA PA n,
    tensorResolutionChartHomologyIso_hom N V MB NB sB PB n]
  rw [Functor.map_comp]
  apply tensorResolutionChartHomologyIso_formula_naturality_of_square
    Y N V U h MA NA MB NB sA sB PA PB n k l hl

end AlgebraicGeometry

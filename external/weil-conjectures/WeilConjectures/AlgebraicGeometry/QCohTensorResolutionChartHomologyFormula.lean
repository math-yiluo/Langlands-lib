/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartModel

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

noncomputable local instance trChartHomFormulaMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trChartHomFormulaZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartHomFormulaObjZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The two factors in the chart homology comparison. -/
theorem tensorResolutionChartHomologyIso_hom {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ProjectiveResolution MA) (n : ℕ) :
    letI : (tilde.functor Γ(Y, U.1)).PreservesHomology :=
      tilde_preservesHomology (Γ(Y, U.1) : Type u)
    let L := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex
    let d := tensorResolutionExtendLeftHomologyData ComplexShape.embeddingDownNat
      L (i := n) (i' := -(n : ℤ)) rfl (L.sc n).homologyData.left
    (tensorResolutionChartHomologyIso N U MA NA sN P n).hom =
      (d.map (tilde.functor Γ(Y, U.1))).homologyIso.inv ≫
        HomologicalComplex.homologyMap
          (tensorResolutionChartTensorIso N U MA NA sN P).hom (-(n : ℤ)) := by
  dsimp only [tensorResolutionChartHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, HomologicalComplex.homologyFunctor]

end AlgebraicGeometry

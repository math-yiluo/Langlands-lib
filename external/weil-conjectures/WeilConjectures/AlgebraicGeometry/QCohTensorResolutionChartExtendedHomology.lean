/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionExtendedCoordinates
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologySquare

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Extension by zero and sheafification are natural for the chart tensor map. -/
theorem tensorResolutionChartExtendedHomology_naturality
    (Y : Scheme.{u}) (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB)
    (k : ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex ⟶
      ((ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex
        (.down ℕ)).obj (((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex))
    (n : ℕ) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let TA := tilde.functor Γ(Y, U.1)
    let TB := tilde.functor Γ(Y, V.1)
    let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
    let LB := ((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex
    letI : TA.PreservesHomology := tilde_preservesHomology _
    letI : TB.PreservesHomology := tilde_preservesHomology _
    let dA := tensorResolutionExtendLeftHomologyData ComplexShape.embeddingDownNat
      LA (i := n) (i' := ComplexShape.embeddingDownNat.f n) rfl (LA.sc n).homologyData.left
    let dB := tensorResolutionExtendLeftHomologyData ComplexShape.embeddingDownNat
      LB (i := n) (i' := ComplexShape.embeddingDownNat.f n) rfl (LB.sc n).homologyData.left
    R.map (dA.map TA).homologyIso.inv ≫
        (((((TA.mapHomologicalComplex (.up ℤ)).obj
          (LA.extend ComplexShape.embeddingDownNat))).sc (-(n : ℤ))).mapHomologyIso R).inv ≫
        HomologicalComplex.homologyMap
          (tensorResolutionSemilinearComplexMap φ (.up ℤ)
            (LA.extend ComplexShape.embeddingDownNat)
            (LB.extend ComplexShape.embeddingDownNat)
            (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k))
          (-(n : ℤ)) =
      tensorResolutionSemilinearMap φ
        (HomologicalComplex.homologyMap k n ≫
          ((LB.sc n).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom) ≫
        (dB.map TB).homologyIso.inv := by
  dsimp only
  exact tensorResolutionExtendedHomology_naturality
    (Y.presheaf.map (homOfLE h).op) ComplexShape.embeddingDownNat
    (((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex)
    (((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex)
    k (i := n) (i' := -(n : ℤ)) rfl

end AlgebraicGeometry

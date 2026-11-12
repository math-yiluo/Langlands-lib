import Langlands.Global.AdelicSpaceIntegerBase
import Langlands.Global.AdelicSpaceUniformModelOpen

/-! # Lifts and openness at actual cofinal principal model levels -/

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open NumberField

noncomputable section

namespace Langlands.Global

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of
  (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)))}

/-- Cofinal principal curve-place levels have actual cofinite factor lifts, with
no lifted-integer algebra or integer-base finite-type premise. -/
def curvePlaceCofinalSpacePointLifts_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hYqs : IsQuasiSeparated Y)
    (hYft : FiniteTypeOverRing
      (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ E : Finset (CurvePlaceLevelFactorIndex k F (curvePlacePrincipalLevelAbove k F S).val),
      (i : CurvePlaceLevelFactorIndex k F (curvePlacePrincipalLevelAbove k F S).val) → i ∉ E →
        (p : RingPoints (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val) Y
          (CurvePlaceLevelFactor k F (curvePlacePrincipalLevelAbove k F S).val i)) →
          {q : RingPoints (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val) X
              (CurvePlaceLevelFactor k F (curvePlacePrincipalLevelAbove k F S).val i) //
            RingPoints.map f q = p} := by
  let := AdelicSpaceIntegerBase.algebra (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)
  let := AdelicSpaceIntegerBase.locallyOfFiniteType
    (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)
  exact curvePlaceSpacePointLifts_of_uniformLangWeil k F (curvePlacePrincipalLevelAbove k F S).val
    hLW hYqs hYft f d chart hchart hdim hsep hqc hsurj hconn

/-- At an actual cofinal principal level above a nonempty initial set, the exact
estimate and fixed-dimensional model geometry suffice for openness. -/
theorem curvePlaceCofinalSpaceLevel_isOpenMap_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X)
    (hXft : FiniteTypeOverRing
      (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val) X)
    (hY : IsSeparated Y)
    (hYft : FiniteTypeOverRing
      (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (curvePlaceSpaceLevelTopology k F (curvePlacePrincipalLevelAbove k F S).val X)
      (curvePlaceSpaceLevelTopology k F (curvePlacePrincipalLevelAbove k F S).val Y) (RingPoints.map f) := by
  let := AdelicSpaceIntegerBase.algebra (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)
  let := AdelicSpaceIntegerBase.locallyOfFiniteType
    (curvePlaceSIntegers k F (curvePlacePrincipalLevelAbove k F S).val)
  have hT : Finset.Nonempty (curvePlacePrincipalLevelAbove k F S).val :=
    hS.mono (curvePlacePrincipalLevelAbove k F S).property
  exact curvePlaceSpaceLevel_isOpenMap_of_uniformLangWeil k F
    (curvePlacePrincipalLevelAbove k F S).val hLW hT hX hXft hY hYft f d chart hchart hdim hsep hqc hsurj hconn

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of
  ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
    Set (FinitePlace K)).integer K)))}

/-- Actual lifts at cofinal number-field principal levels retain the full factor
index and the original coefficient action, with no integer-base premise. -/
def numberFieldCofinalSpacePointLifts_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hYqs : IsQuasiSeparated Y)
    (hYft : FiniteTypeOverRing
      ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    Σ E : Finset (NumberFieldLevelFactorIndex K (numberFieldPrincipalLevelAbove K S).val),
      (i : NumberFieldLevelFactorIndex K (numberFieldPrincipalLevelAbove K S).val) → i ∉ E →
        (p : RingPoints
          ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
            Set (FinitePlace K)).integer K) Y
          (NumberFieldLevelFactor K (numberFieldPrincipalLevelAbove K S).val i)) →
          {q : RingPoints
              ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
                Set (FinitePlace K)).integer K) X
              (NumberFieldLevelFactor K (numberFieldPrincipalLevelAbove K S).val i) //
            RingPoints.map f q = p} := by
  let := AdelicSpaceIntegerBase.algebra
    ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
      Set (FinitePlace K)).integer K)
  let := AdelicSpaceIntegerBase.locallyOfFiniteType
    ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
      Set (FinitePlace K)).integer K)
  exact numberFieldSpacePointLifts_of_uniformLangWeil K (numberFieldPrincipalLevelAbove K S).val
    hLW hYqs hYft f d chart hchart hdim hsep hqc hsurj hconn

/-- At actual cofinal number-field principal levels, the exact estimate and
fixed-dimensional model geometry suffice for openness. -/
theorem numberFieldCofinalSpaceLevel_isOpenMap_of_uniformLangWeil
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X)
    (hXft : FiniteTypeOverRing
      ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y)
    (hYft : FiniteTypeOverRing
      ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (d : ℕ) (chart : EtaleMorphismChart f)
    (hchart : IsSurjective chart.sourceMap) (hdim : SmoothOfRelativeDimension d chart.schemeMap.left)
    (hsep : IsSeparatedMorphism f) (hqc : IsQuasiCompactMorphism f)
    (hsurj : IsSurjectiveMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (numberFieldSpaceLevelTopology K (numberFieldPrincipalLevelAbove K S).val X)
      (numberFieldSpaceLevelTopology K (numberFieldPrincipalLevelAbove K S).val Y) (RingPoints.map f) := by
  let := AdelicSpaceIntegerBase.algebra
    ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
      Set (FinitePlace K)).integer K)
  let := AdelicSpaceIntegerBase.locallyOfFiniteType
    ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
      Set (FinitePlace K)).integer K)
  exact numberFieldSpaceLevel_isOpenMap_of_uniformLangWeil K (numberFieldPrincipalLevelAbove K S).val
    hLW hX hXft hY hYft f d chart hchart hdim hsep hqc hsurj hconn

end NumberField

end Langlands.Global

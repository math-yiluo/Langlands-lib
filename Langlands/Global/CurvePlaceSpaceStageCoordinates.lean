import Langlands.Global.AdelicSpaceStageCoordinates

/-! # Original fixed-base coordinates of curve-place algebraic-space stages -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped Langlands.Global.FixedModelLocalProduct

namespace Langlands.Global.AdelicSpaceStageCoordinates

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

section CurvePlace

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (S : Finset (AlgebraicCurve.Place k F)) (T : AdelicLevelIndexAbove S)

/-- The original enlarged-level fields with the fixed original coefficient action. -/
scoped instance curveFieldAlgebra (i : CurvePlaceLevelFactorIndex k F T.val) :
    Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F T.val i) :=
  ((algebraMap (curvePlaceSIntegers k F T.val)
    (CurvePlaceLevelField k F T.val i)).comp (curvePlaceSIntegersMap k F T.property)).toAlgebra

scoped instance curveFieldTower (i : CurvePlaceLevelFactorIndex k F T.val) :
    IsScalarTower (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (CurvePlaceLevelField k F T.val i) :=
  .of_algebraMap_eq fun _ => rfl

variable (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
  [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (hS : S.Nonempty)

/-- An arithmetic stage has the product of its original fixed-base
field-valued coordinate topologies. -/
def curveStageHomeomorph :
    letI := curvePlaceSpaceStageTopology k F S X T
    letI : ∀ i : CurvePlaceLevelFactorIndex k F T.val, TopologicalSpace
        (RingPoints (curvePlaceSIntegers k F S) X
          (CurvePlaceLevelFactor k F T.val i)) :=
      fun i => fieldValuedPointTopology (curvePlaceSIntegers k F S) X
        ((curvePlaceLevelFieldAlgHom k F T.val i).restrictScalars _)
    RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) ≃ₜ
      (∀ i : CurvePlaceLevelFactorIndex k F T.val,
        RingPoints (curvePlaceSIntegers k F S) X
          (CurvePlaceLevelFactor k F T.val i)) := by
  let R := (curvePlaceSIntegers k F S)
  let R' := (curvePlaceSIntegers k F T.val)
  let X' := curvePlaceSpaceLevelBaseChange k F T.property X
  let : TopologicalSpace (RingPoints R X (curvePlaceAdeleLevelOver k F S T)) :=
    curvePlaceSpaceStageTopology k F S X T
  let : TopologicalSpace (RingPoints R' X' (curvePlaceAdeleLevel k F T.val)) :=
    curvePlaceSpaceLevelTopology k F T.val X'
  let (i : CurvePlaceLevelFactorIndex k F T.val) :
      TopologicalSpace (RingPoints R' X' (CurvePlaceLevelFactor k F T.val i)) :=
    fieldValuedPointTopology R' X' (curvePlaceLevelFieldAlgHom k F T.val i)
  let (i : CurvePlaceLevelFactorIndex k F T.val) :
      TopologicalSpace (RingPoints R X (CurvePlaceLevelFactor k F T.val i)) :=
    fieldValuedPointTopology R X ((curvePlaceLevelFieldAlgHom k F T.val i).restrictScalars R)
  let H := (curvePlaceSpaceStageEquiv k F S X T).toHomeomorphOfIsInducing ⟨rfl⟩
  exact (H.trans
    (coordinatePointHomeomorph (CurvePlaceLevelFactor k F T.val) (CurvePlaceLevelField k F T.val)
      (curvePlaceLevelFieldAlgHom k F T.val) (curvePlaceLevelFactorAlgHom k F T.val) X'
      (curvePlaceSpaceLevelPoints k F T.val (hS.mono T.property) X'
        hsep.baseChange hft.baseChange))).trans
    (Homeomorph.piCongrRight fun i =>
      fieldValuedBaseChangeHomeomorph R R' X (curvePlaceLevelFieldAlgHom k F T.val i))

@[simp]
theorem curveStageHomeomorph_apply
    (x : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
    (i : CurvePlaceLevelFactorIndex k F T.val) :
    curveStageHomeomorph k F S T X hsep hft hS x i =
      RingPoints.changeRing
        ((Pi.evalAlgHom (curvePlaceSIntegers k F S)
          (CurvePlaceLevelFactor k F T.val) i).comp
          (FixedModelLocalProduct.curveFactorAlgEquiv k F S T).toAlgHom) x := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F T.val) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevelOver k F S T))
  let : IsScalarTower (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val) :=
    .of_algebraMap_eq fun _ => rfl
  change baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (CurvePlaceLevelFactor k F T.val i) X
      (RingPoints.changeRing (curvePlaceLevelFactorAlgHom k F T.val i)
        (curvePlaceSpaceStageEquiv k F S X T x)) = _
  rw [baseChangeRingPointsEquiv_changeRing]
  have hcancel : baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val) X
      (curvePlaceSpaceStageEquiv k F S X T x) = x :=
    (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) X).apply_symm_apply x
  rw [hcancel]
  rfl

end CurvePlace

end Langlands.Global.AdelicSpaceStageCoordinates

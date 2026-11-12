import Langlands.Global.CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup
import Langlands.Global.CurvePlaceFixedModelWeilEvaluation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionEvaluation

/-! # Original counit evaluation on curve-place space stages -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicSpaceStageCoordinates

namespace Langlands.Global.CurvePlaceSpaceFixedModelWeilEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open CurvePlacePrincipalSIntegerFixedLevelWeil
open CurvePlacePrincipalSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup (upperLevel indexEquiv)

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))

/-- The original full inclusion restricted to a level and its full upper preimage. -/
def levelInclusion :
    curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T →+*
      curvePlaceAdeleLevelOver k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        (upperLevel k K L s t T) :=
  curvePlaceAdeleLevelInclusion (L := L) T.val

/-- The literal level inclusion respects the two original integral bases. -/
theorem levelInclusion_compatible :
    (levelInclusion k K L s t T).comp
        (algebraMap (lowerCoefficients k K s t)
          (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) =
      (algebraMap (upperCoefficients k K L s t)
        (curvePlaceAdeleLevelOver k L
          (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
          (upperLevel k K L s t T))).comp
        (algebraMap (lowerCoefficients k K s t) (upperCoefficients k K L s t)) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro q
  exact curvePlaceCompletionInclusion_algebraMap q a.val

/-- The literal upper-stage coordinate with the original fixed integral base. -/
def upperStageFactorAlgHom
    (j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val) :
    curvePlaceAdeleLevelOver k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        (upperLevel k K L s t T) →ₐ[upperCoefficients k K L s t]
      CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j :=
  (Pi.evalAlgHom (upperCoefficients k K L s t)
    (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val) j).comp
    (FixedModelLocalProduct.curveFactorAlgEquiv k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      (upperLevel k K L s t T)).toAlgHom

/-- Each upper projection after inclusion is the original local coefficient. -/
theorem levelInclusion_coordinate (z : Σ i, Above k K L s t T i) :
    ((upperStageFactorAlgHom k K L s t T (indexEquiv k K L s t T z)).toRingHom.comp
        (levelInclusion k K L s t T)) =
      (show _ →+* CurvePlaceLevelFactor k L (upperLevel k K L s t T).val
        (indexEquiv k K L s t T z) from by
          rcases z with ⟨i, q⟩
          cases i with
          | inl v => exact CurvePlaceFixedLevelWeilEvaluation.localCoefficient k K L s t T (.inl v) q
          | inr v => exact CurvePlaceFixedLevelWeilEvaluation.localCoefficient k K L s t T (.inr v) q) := by
  rcases z with ⟨i, q⟩
  cases i with
  | inl v =>
    apply RingHom.ext
    intro a
    exact congrArg (fun f => f a.val)
      (CurvePlaceFixedModelWeilEvaluation.fullUpperFieldCoefficient_eq_projection
        k K L s t v.1 q).symm
  | inr v =>
    apply RingHom.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun f => f a.val)
      (CurvePlaceFixedModelWeilEvaluation.fullUpperFieldCoefficient_eq_projection
        k K L s t v.1 q).symm

/-- The upper projection expressed in the original regrouped coefficient algebra. -/
def upperLevelFactorAlgHom (i : CurvePlaceLevelFactorIndex k K T.val)
    (q : Above k K L s t T i) :
    curvePlaceAdeleLevelOver k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        (upperLevel k K L s t T) →ₐ[upperCoefficients k K L s t]
      upperFactor k K L s t T i q := by
  cases i with
  | inl v =>
    exact { (upperStageFactorAlgHom k K L s t T
      (indexEquiv k K L s t T ⟨.inl v, q⟩)).toRingHom with
      commutes' := fun _ => rfl }
  | inr v =>
    exact { (upperStageFactorAlgHom k K L s t T
      (indexEquiv k K L s t T ⟨.inr v, q⟩)).toRingHom with
      commutes' := fun _ => rfl }

variable (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients k K L s t))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients k K s t) (upperCoefficients k K L s t)).obj X.toSheaf))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients k K L s t) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients k K s t)
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  (hS : (curvePlacePrincipalExceptional k K s (t : K)).Nonempty)

set_option maxHeartbeats 200000 in
/-- The constructed stage homeomorphism is the original counit along the literal level inclusion. -/
theorem adelicLevelPointHomeomorph_eq_evaluation
    (x : RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup.adelicLevelPointHomeomorph k K L s t T X h
        hsep hft hWsep hWft hS x =
      spaceWeilRestrictionEvaluation (lowerCoefficients k K s t) (upperCoefficients k K L s t)
        (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
        (curvePlaceAdeleLevelOver k L
          (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
          (upperLevel k K L s t T))
        (levelInclusion k K L s t T) (levelInclusion_compatible k K L s t T) X h x := by
  let := curvePlaceSpaceStageTopology k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X
    (upperLevel k K L s t T)
  let (j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X
        (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X
      ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val j).restrictScalars _)
  apply (AdelicSpaceStageCoordinates.curveStageHomeomorph k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
    (upperLevel k K L s t T) X hsep hft
    (CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup.upperSupport_nonempty k K L s t hS)).injective
  funext j
  obtain ⟨⟨i, q⟩, rfl⟩ := (indexEquiv k K L s t T).surjective j
  have hc := congrFun
    (CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup.adelicLevelPointHomeomorph_coordinates
      k K L s t T X h hsep hft hWsep hWft hS x) (indexEquiv k K L s t T ⟨i, q⟩)
  rw [CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup.productPointHomeomorph_apply,
    CurvePlacePrincipalSIntegerSpaceFixedLevelWeil.levelPointHomeomorph_component] at hc
  rw [hc, AdelicSpaceStageCoordinates.curveStageHomeomorph_apply]
  rw [completedTensorSpaceWeilRestrictionPointMap_eq_evaluation
    (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
    (CurvePlaceLevelFactor k K T.val i) (upperFactor k K L s t T i)
    (tensorEquiv k K L s t T i) (tensorEquiv_one_tmul k K L s t T i)
    (levelFactorAlgHom k K s t T i) q
    (CurvePlaceFixedLevelWeilEvaluation.localCoefficient k K L s t T i q)
    (CurvePlaceFixedLevelWeilEvaluation.localCoefficient_compatible k K L s t T i q) rfl X h x]
  cases i with
  | inl v =>
    change spaceWeilRestrictionEvaluation _ _ _ _
        (CurvePlaceFixedLevelWeilEvaluation.localCoefficient k K L s t T (.inl v) q)
        (CurvePlaceFixedLevelWeilEvaluation.localCoefficient_compatible k K L s t T (.inl v) q)
        X h x = _
    exact (spaceWeilRestrictionEvaluation_natural_upper
      (lowerCoefficients k K s t) (upperCoefficients k K L s t)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
      (curvePlaceAdeleLevelOver k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        (upperLevel k K L s t T))
      (upperFactor k K L s t T (.inl v) q)
      (levelInclusion k K L s t T)
      (CurvePlaceFixedLevelWeilEvaluation.localCoefficient k K L s t T (.inl v) q)
      (levelInclusion_compatible k K L s t T)
      (CurvePlaceFixedLevelWeilEvaluation.localCoefficient_compatible k K L s t T (.inl v) q)
      (upperLevelFactorAlgHom k K L s t T (.inl v) q)
      (levelInclusion_coordinate k K L s t T ⟨(.inl v), q⟩) X h x).symm
  | inr v =>
    change spaceWeilRestrictionEvaluation _ _ _ _
        (CurvePlaceFixedLevelWeilEvaluation.localCoefficient k K L s t T (.inr v) q)
        (CurvePlaceFixedLevelWeilEvaluation.localCoefficient_compatible k K L s t T (.inr v) q)
        X h x = _
    exact (spaceWeilRestrictionEvaluation_natural_upper
      (lowerCoefficients k K s t) (upperCoefficients k K L s t)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
      (curvePlaceAdeleLevelOver k L
        (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
        (upperLevel k K L s t T))
      (upperFactor k K L s t T (.inr v) q)
      (levelInclusion k K L s t T)
      (CurvePlaceFixedLevelWeilEvaluation.localCoefficient k K L s t T (.inr v) q)
      (levelInclusion_compatible k K L s t T)
      (CurvePlaceFixedLevelWeilEvaluation.localCoefficient_compatible k K L s t T (.inr v) q)
      (upperLevelFactorAlgHom k K L s t T (.inr v) q)
      (levelInclusion_coordinate k K L s t T ⟨(.inr v), q⟩) X h x).symm

/-- The original integral Weil counit along the literal full curve adele inclusion. -/
def adelicEvaluation
    (x : CurvePlaceSpaceAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)) :
    CurvePlaceSpaceAdelePoints k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X :=
  spaceWeilRestrictionEvaluation (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K)))
    (curvePlaceAdeleOver k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
    (curvePlaceAdeleInclusion (k := k) (K := K) (L := L))
    (CurvePlaceFixedModelWeilEvaluation.adeleInclusion_compatible k K L s t) X h x

/-- Full evaluation commutes with each original stage homeomorphism and its literal inclusions. -/
theorem adelicEvaluation_stage
    (x : RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    adelicEvaluation k K L s t X h
        (RingPoints.changeRing (curvePlaceAdeleLevelOverι k K
          (curvePlacePrincipalExceptional k K s (t : K)) T).hom x) =
      RingPoints.changeRing
        (curvePlaceAdeleLevelOverι k L
          (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
          (upperLevel k K L s t T)).hom
        (CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup.adelicLevelPointHomeomorph
          k K L s t T X h hsep hft hWsep hWft hS x) := by
  rw [adelicLevelPointHomeomorph_eq_evaluation k K L s t T X h hsep hft hWsep hWft hS]
  let f := (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)).comp
    (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom.toRingHom
  have hf : f.comp (algebraMap (lowerCoefficients k K s t)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) =
      (algebraMap (upperCoefficients k K L s t)
        (curvePlaceAdeleOver k L
          (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))).comp
        (algebraMap (lowerCoefficients k K s t) (upperCoefficients k K L s t)) := by
    apply RingHom.ext
    intro a
    apply RestrictedProduct.ext
    intro q
    exact curvePlaceCompletionInclusion_algebraMap q a.val
  change spaceWeilRestrictionEvaluation _ _ _ _ _ _ X h
      (RingPoints.changeRing (curvePlaceAdeleLevelOverι k K
        (curvePlacePrincipalExceptional k K s (t : K)) T).hom x) = _
  rw [spaceWeilRestrictionEvaluation_natural_lower
    (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
    (curvePlaceAdeleOver k K (curvePlacePrincipalExceptional k K s (t : K)))
    (curvePlaceAdeleOver k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
    f (curvePlaceAdeleInclusion (k := k) (K := K) (L := L)) hf
    (CurvePlaceFixedModelWeilEvaluation.adeleInclusion_compatible k K L s t)
    (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom rfl X h x]
  exact (spaceWeilRestrictionEvaluation_natural_upper
    (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)
    (curvePlaceAdeleLevelOver k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      (upperLevel k K L s t T))
    (curvePlaceAdeleOver k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
    (levelInclusion k K L s t T) f (levelInclusion_compatible k K L s t T) hf
    (curvePlaceAdeleLevelOverι k L
      (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      (upperLevel k K L s t T)).hom rfl X h x).symm

end Langlands.Global.CurvePlaceSpaceFixedModelWeilEvaluation

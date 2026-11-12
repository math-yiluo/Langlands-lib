import Langlands.Global.NumberFieldSIntegerSpaceFixedLevelRegroup
import Langlands.Global.NumberFieldFixedModelWeilEvaluation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionEvaluation

/-! # Original counit evaluation on number-field space stages -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLevelWeil
  Langlands.Global.NumberFieldSIntegerFixedLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicSpaceStageCoordinates

namespace Langlands.Global.NumberFieldSpaceFixedModelWeilEvaluation

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open AdelicFunctoriality NumberFieldSIntegerLevelWeil NumberFieldSIntegerFixedLevelWeil
open NumberFieldSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open NumberFieldSIntegerSpaceFixedLevelRegroup (upperLevel indexEquiv)

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

/-- The original full adele inclusion restricted to a level and its full upper preimage. -/
def levelInclusion :
    numberFieldAdeleLevelOver K S T →+*
      numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
        (upperLevel K L S T) :=
  (adeleInclusion (K := K) (L := L)).restrict
    (numberFieldAdeleLevel K T.val)
    (numberFieldAdeleLevel L (numberFieldExceptionalPreimage (L := L) T.val)) (by
      intro a ha q hq
      exact (AdelicFunctoriality.FiniteExtension.completionMap_mem_integers_iff
        (q.under (NumberField.RingOfIntegers K)) q _).mpr
        (ha _ (by simpa only [mem_numberFieldExceptionalPreimage] using hq)))

/-- The literal level inclusion respects the original two integral bases. -/
theorem levelInclusion_compatible :
    (levelInclusion K L S T).comp
        (algebraMap (lowerCoefficients K S) (numberFieldAdeleLevelOver K S T)) =
      (algebraMap (upperCoefficients K L S)
        (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
          (upperLevel K L S T))).comp
        (algebraMap (lowerCoefficients K S) (upperCoefficients K L S)) := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact adeleInclusion_diagonal (K := K) (L := L) a.val

/-- Original upper-coordinate projection after the level inclusion is the original local coefficient. -/
theorem levelInclusion_coordinate (z : Σ i, Above K L T.val i) :
    ((levelFactorAlgHom L (numberFieldExceptionalPreimage (L := L) S)
      (upperLevel K L S T) (indexEquiv K L S T z)).toRingHom.comp
        (levelInclusion K L S T)) =
      (show numberFieldAdeleLevelOver K S T →+*
        NumberFieldLevelFactor L (upperLevel K L S T).val (indexEquiv K L S T z) from
        by
          rcases z with ⟨i, q⟩
          cases i with
          | inl v => exact NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inl v) q
          | inr z => cases z with
            | inl v => exact NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inr (.inl v)) q
            | inr v => exact NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inr (.inr v)) q) := by
  rcases z with ⟨i, q⟩
  cases i with
  | inl v =>
    apply RingHom.ext
    intro a
    exact congrArg (fun f => f a.val)
      (NumberFieldFixedModelWeilEvaluation.fullUpperFieldCoefficient_eq_projection K L S
        (.inl v) q).symm
  | inr z =>
    cases z with
    | inl v =>
      apply RingHom.ext
      intro a
      exact congrArg (fun f => f a.val)
        (NumberFieldFixedModelWeilEvaluation.fullUpperFieldCoefficient_eq_projection K L S
          (.inr v.1) q).symm
    | inr v =>
      apply RingHom.ext
      intro a
      apply Subtype.ext
      exact congrArg (fun f => f a.val)
        (NumberFieldFixedModelWeilEvaluation.fullUpperFieldCoefficient_eq_projection K L S
          (.inr v.1) q).symm


/-- The upper level projection expressed in the original regrouped coefficient algebra. -/
def upperLevelFactorAlgHom (i : NumberFieldLevelFactorIndex K T.val)
    (q : Above K L T.val i) :
    numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
      (upperLevel K L S T) →ₐ[upperCoefficients K L S] upperFactor K L T.val i q := by
  cases i with
  | inl v =>
    exact { (levelFactorAlgHom L (numberFieldExceptionalPreimage (L := L) S)
      (upperLevel K L S T) (indexEquiv K L S T ⟨.inl v, q⟩)).toRingHom with
      commutes' := fun _ => rfl }
  | inr z => cases z with
    | inl v =>
      exact { (levelFactorAlgHom L (numberFieldExceptionalPreimage (L := L) S)
        (upperLevel K L S T) (indexEquiv K L S T ⟨.inr (.inl v), q⟩)).toRingHom with
        commutes' := fun _ => rfl }
    | inr v =>
      exact { (levelFactorAlgHom L (numberFieldExceptionalPreimage (L := L) S)
        (upperLevel K L S T) (indexEquiv K L S T ⟨.inr (.inr v), q⟩)).toRingHom with
        commutes' := fun _ => rfl }


variable (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients K L S))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients K S) (upperCoefficients K L S)).obj X.toSheaf))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients K L S) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients K S)
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))

set_option maxHeartbeats 200000 in
/-- The constructed stage homeomorphism is exactly the original counit along the literal level inclusion. -/
theorem adelicLevelPointHomeomorph_eq_evaluation
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (numberFieldAdeleLevelOver K S T)) :
    NumberFieldSIntegerSpaceFixedLevelRegroup.adelicLevelPointHomeomorph K L S T X h
        hsep hft hWsep hWft x =
      spaceWeilRestrictionEvaluation (lowerCoefficients K S) (upperCoefficients K L S)
        (numberFieldAdeleLevelOver K S T)
        (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
          (upperLevel K L S T))
        (levelInclusion K L S T) (levelInclusion_compatible K L S T) X h x := by
  let := numberFieldSpaceStageTopology L (numberFieldExceptionalPreimage (L := L) S) X
    (upperLevel K L S T)
  let (j : NumberFieldLevelFactorIndex L (upperLevel K L S T).val) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X
        (NumberFieldLevelFactor L (upperLevel K L S T).val j)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X
      ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val j).restrictScalars _)
  apply (AdelicSpaceStageCoordinates.numberFieldStageHomeomorph L
    (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) X hsep hft).injective
  funext j
  obtain ⟨⟨i, q⟩, rfl⟩ := (indexEquiv K L S T).surjective j
  have hc := congrFun
    (NumberFieldSIntegerSpaceFixedLevelRegroup.adelicLevelPointHomeomorph_coordinates
      K L S T X h hsep hft hWsep hWft x) (indexEquiv K L S T ⟨i, q⟩)
  rw [NumberFieldSIntegerSpaceFixedLevelRegroup.productPointHomeomorph_apply,
    NumberFieldSIntegerSpaceFixedLevelWeil.levelPointHomeomorph_component] at hc
  rw [hc, AdelicSpaceStageCoordinates.numberFieldStageHomeomorph_apply]
  rw [completedTensorSpaceWeilRestrictionPointMap_eq_evaluation
    (lowerCoefficients K S) (upperCoefficients K L S) (numberFieldAdeleLevelOver K S T)
    (NumberFieldLevelFactor K T.val i) (upperFactor K L T.val i)
    (tensorEquiv K L S T i) (tensorEquiv_one_tmul K L S T i)
    (levelFactorAlgHom K S T i) q
    (NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T i q)
    (NumberFieldFixedLevelWeilEvaluation.localCoefficient_compatible K L S T i q) rfl X h x]
  cases i with
  | inl v =>
    change spaceWeilRestrictionEvaluation _ _ _ _
        (NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inl v) q)
        (NumberFieldFixedLevelWeilEvaluation.localCoefficient_compatible K L S T (.inl v) q)
        X h x = _
    exact (spaceWeilRestrictionEvaluation_natural_upper
      (lowerCoefficients K S) (upperCoefficients K L S) (numberFieldAdeleLevelOver K S T)
      (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
        (upperLevel K L S T))
      (upperFactor K L T.val (.inl v) q)
      (levelInclusion K L S T)
      (NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inl v) q)
      (levelInclusion_compatible K L S T)
      (NumberFieldFixedLevelWeilEvaluation.localCoefficient_compatible K L S T (.inl v) q)
      (upperLevelFactorAlgHom K L S T (.inl v) q)
      (levelInclusion_coordinate K L S T ⟨(.inl v), q⟩) X h x).symm
  | inr z =>
    cases z with
    | inl v =>
      change spaceWeilRestrictionEvaluation _ _ _ _
          (NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inr (.inl v)) q)
          (NumberFieldFixedLevelWeilEvaluation.localCoefficient_compatible K L S T (.inr (.inl v)) q)
          X h x = _
      exact (spaceWeilRestrictionEvaluation_natural_upper
        (lowerCoefficients K S) (upperCoefficients K L S) (numberFieldAdeleLevelOver K S T)
        (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
          (upperLevel K L S T))
        (upperFactor K L T.val (.inr (.inl v)) q)
        (levelInclusion K L S T)
        (NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inr (.inl v)) q)
        (levelInclusion_compatible K L S T)
        (NumberFieldFixedLevelWeilEvaluation.localCoefficient_compatible K L S T (.inr (.inl v)) q)
        (upperLevelFactorAlgHom K L S T (.inr (.inl v)) q)
        (levelInclusion_coordinate K L S T ⟨(.inr (.inl v)), q⟩) X h x).symm
    | inr v =>
      change spaceWeilRestrictionEvaluation _ _ _ _
          (NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inr (.inr v)) q)
          (NumberFieldFixedLevelWeilEvaluation.localCoefficient_compatible K L S T (.inr (.inr v)) q)
          X h x = _
      exact (spaceWeilRestrictionEvaluation_natural_upper
        (lowerCoefficients K S) (upperCoefficients K L S) (numberFieldAdeleLevelOver K S T)
        (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
          (upperLevel K L S T))
        (upperFactor K L T.val (.inr (.inr v)) q)
        (levelInclusion K L S T)
        (NumberFieldFixedLevelWeilEvaluation.localCoefficient K L S T (.inr (.inr v)) q)
        (levelInclusion_compatible K L S T)
        (NumberFieldFixedLevelWeilEvaluation.localCoefficient_compatible K L S T (.inr (.inr v)) q)
        (upperLevelFactorAlgHom K L S T (.inr (.inr v)) q)
        (levelInclusion_coordinate K L S T ⟨(.inr (.inr v)), q⟩) X h x).symm


/-- The original integral Weil counit evaluated along the literal full adele inclusion. -/
def adelicEvaluation
    (x : NumberFieldSpaceAdelePoints K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)) :
    NumberFieldSpaceAdelePoints L (numberFieldExceptionalPreimage (L := L) S) X :=
  spaceWeilRestrictionEvaluation (lowerCoefficients K S) (upperCoefficients K L S)
    (numberFieldAdeleOver K S)
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))
    (adeleInclusion (K := K) (L := L))
    (NumberFieldFixedModelWeilEvaluation.adeleInclusion_compatible K L S) X h x

/-- On each original arithmetic stage, full evaluation is the constructed stage homeomorphism
followed by the literal upper stage inclusion. -/
theorem adelicEvaluation_stage
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (numberFieldAdeleLevelOver K S T)) :
    adelicEvaluation K L S X h
        (RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom x) =
      RingPoints.changeRing
        (numberFieldAdeleLevelOverι L (numberFieldExceptionalPreimage (L := L) S)
          (upperLevel K L S T)).hom
        (NumberFieldSIntegerSpaceFixedLevelRegroup.adelicLevelPointHomeomorph K L S T X h
          hsep hft hWsep hWft x) := by
  rw [adelicLevelPointHomeomorph_eq_evaluation K L S T X h hsep hft hWsep hWft]
  let f := (adeleInclusion (K := K) (L := L)).comp
    (numberFieldAdeleLevelOverι K S T).hom.toRingHom
  have hf : f.comp (algebraMap (lowerCoefficients K S) (numberFieldAdeleLevelOver K S T)) =
      (algebraMap (upperCoefficients K L S)
        (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))).comp
        (algebraMap (lowerCoefficients K S) (upperCoefficients K L S)) := by
    apply RingHom.ext
    intro a
    exact adeleInclusion_diagonal (K := K) (L := L) a.val
  change spaceWeilRestrictionEvaluation _ _ _ _ _ _ X h
      (RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom x) = _
  rw [spaceWeilRestrictionEvaluation_natural_lower
    (lowerCoefficients K S) (upperCoefficients K L S)
    (numberFieldAdeleLevelOver K S T) (numberFieldAdeleOver K S)
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))
    f (adeleInclusion (K := K) (L := L)) hf
    (NumberFieldFixedModelWeilEvaluation.adeleInclusion_compatible K L S)
    (numberFieldAdeleLevelOverι K S T).hom rfl X h x]
  exact (spaceWeilRestrictionEvaluation_natural_upper
    (lowerCoefficients K S) (upperCoefficients K L S) (numberFieldAdeleLevelOver K S T)
    (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
      (upperLevel K L S T))
    (numberFieldAdeleOver L (numberFieldExceptionalPreimage (L := L) S))
    (levelInclusion K L S T) f (levelInclusion_compatible K L S T) hf
    (numberFieldAdeleLevelOverι L (numberFieldExceptionalPreimage (L := L) S)
      (upperLevel K L S T)).hom rfl X h x).symm

end Langlands.Global.NumberFieldSpaceFixedModelWeilEvaluation

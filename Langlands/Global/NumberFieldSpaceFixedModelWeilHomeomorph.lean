import Langlands.Global.NumberFieldSpaceFixedModelWeilEvaluation
import Langlands.Global.AdelicWeilLevelCofinality
import Langlands.Global.AdelicSpacePointTopologyTheorem
import Langlands.Topology.FinalStageComparison

/-! # Full adelic homeomorphism for an original number-field space Weil model -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField Langlands.Global Langlands.Global.NumberFieldSIntegers

namespace Langlands.Global.NumberFieldSpaceFixedModelWeilHomeomorph

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open NumberFieldSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open NumberFieldSIntegerSpaceFixedLevelRegroup (upperLevel adelicLevelPointHomeomorph)
open NumberFieldSpaceFixedModelWeilEvaluation AdelicWeilLevelCofinality
open AdelicSpacePointStagesProof AdelicSpacePointTopologyProof Langlands.Topology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients K L S))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients K S) (upperCoefficients K L S)).obj X.toSheaf))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients K L S) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients K S)
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))

local instance lowerStageTopology (T : AdelicLevelIndexAbove S) :
    TopologicalSpace (RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (numberFieldAdeleLevelOver K S T)) :=
  numberFieldSpaceStageTopology K S _ T

local instance upperStageTopology
    (U : AdelicLevelIndexAbove (numberFieldExceptionalPreimage (L := L) S)) :
    TopologicalSpace (RingPoints (upperCoefficients K L S) X
      (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S) U)) :=
  numberFieldSpaceStageTopology L (numberFieldExceptionalPreimage (L := L) S) X U

include hsep hft hWsep hWft

/-- The original full counit evaluation is injective. -/
theorem adelicEvaluation_injective :
    Function.Injective (adelicEvaluation K L S X h) := by
  intro a b hab
  obtain ⟨T, x, rfl⟩ := numberField_cover spaceFilteredRingPointComparison K S hWft a
  obtain ⟨U, y, rfl⟩ := numberField_cover spaceFilteredRingPointComparison K S hWft b
  obtain ⟨V, hTV, hUV⟩ := exists_ge_ge T U
  let xV := RingPoints.changeRing (numberFieldAdeleLevelOverMap K S hTV).hom x
  let yV := RingPoints.changeRing (numberFieldAdeleLevelOverMap K S hUV).hom y
  have hx : numberFieldSpaceStageMap K S _ V xV = numberFieldSpaceStageMap K S _ T x :=
    AdelicSpacePointsProof.numberField_stageMap_transition K S hTV x
  have hy : numberFieldSpaceStageMap K S _ V yV = numberFieldSpaceStageMap K S _ U y :=
    AdelicSpacePointsProof.numberField_stageMap_transition K S hUV y
  rw [← hx, ← hy] at hab ⊢
  apply congrArg (numberFieldSpaceStageMap K S _ V)
  apply (adelicLevelPointHomeomorph K L S V X h hsep hft hWsep hWft).injective
  apply RelativeIntegralPoints.changeRing_injective hsep
    (numberFieldAdeleLevelOverι L (numberFieldExceptionalPreimage (L := L) S)
      (upperLevel K L S V)).hom (fun _ _ he => Subtype.ext he)
  exact (adelicEvaluation_stage K L S V X h hsep hft hWsep hWft xV).symm.trans
    (hab.trans (adelicEvaluation_stage K L S V X h hsep hft hWsep hWft yV))

/-- Cofinal original upper stages are all in the image of the full counit evaluation. -/
theorem adelicEvaluation_surjective :
    Function.Surjective (adelicEvaluation K L S X h) := by
  intro b
  obtain ⟨U, y, rfl⟩ := numberField_cover spaceFilteredRingPointComparison L
    (numberFieldExceptionalPreimage (L := L) S) hft b
  let T := numberFieldLevelCover K L S U
  let e := adelicLevelPointHomeomorph K L S T X h hsep hft hWsep hWft
  let yV := RingPoints.changeRing
    (numberFieldAdeleLevelOverMap L (numberFieldExceptionalPreimage (L := L) S)
      (numberFieldLevelCover_spec K L S U)).hom y
  refine ⟨numberFieldSpaceStageMap K S _ T (e.symm yV), ?_⟩
  change adelicEvaluation K L S X h
    (RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom (e.symm yV)) = _
  rw [adelicEvaluation_stage K L S T X h hsep hft hWsep hWft]
  change numberFieldSpaceStageMap L (numberFieldExceptionalPreimage (L := L) S) X
    (upperLevel K L S T) (e (e.symm yV)) = _
  rw [e.apply_symm_apply]
  exact AdelicSpacePointsProof.numberField_stageMap_transition L
    (numberFieldExceptionalPreimage (L := L) S) (X := X)
    (numberFieldLevelCover_spec K L S U) y

/-- The original counit is an equivalence on full integral-model adelic points. -/
def adelicPointEquiv :
    NumberFieldSpaceAdelePoints K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) ≃
      NumberFieldSpaceAdelePoints L (numberFieldExceptionalPreimage (L := L) S) X :=
  Equiv.ofBijective (adelicEvaluation K L S X h)
    ⟨adelicEvaluation_injective K L S X h hsep hft hWsep hWft,
      adelicEvaluation_surjective K L S X h hsep hft hWsep hWft⟩

/-- Every lower stage has the original continuous Weil comparison as a full-evaluation lift. -/
theorem forward_stage_lifts :
    HasContinuousStageLifts (numberFieldSpaceStageMap K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
      (numberFieldSpaceStageMap L (numberFieldExceptionalPreimage (L := L) S) X)
      (adelicPointEquiv K L S X h hsep hft hWsep hWft) := by
  intro T
  exact ⟨upperLevel K L S T, adelicLevelPointHomeomorph K L S T X h hsep hft hWsep hWft,
    (adelicLevelPointHomeomorph K L S T X h hsep hft hWsep hWft).continuous,
    adelicEvaluation_stage K L S T X h hsep hft hWsep hWft⟩

/-- Each upper stage lifts continuously through a cofinal full-preimage stage and its inverse. -/
theorem backward_stage_lifts :
    HasContinuousStageLifts
      (numberFieldSpaceStageMap L (numberFieldExceptionalPreimage (L := L) S) X)
      (numberFieldSpaceStageMap K S
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
      (adelicPointEquiv K L S X h hsep hft hWsep hWft).symm := by
  intro U
  let T := numberFieldLevelCover K L S U
  let e := adelicLevelPointHomeomorph K L S T X h hsep hft hWsep hWft
  let g := RingPoints.changeRing (X := X)
    (numberFieldAdeleLevelOverMap L (numberFieldExceptionalPreimage (L := L) S)
      (numberFieldLevelCover_spec K L S U)).hom
  refine ⟨T, e.symm ∘ g, e.symm.continuous.comp
    (numberField_stage_transition L (numberFieldExceptionalPreimage (L := L) S)
      hsep hft (numberFieldLevelCover_spec K L S U)).continuous, ?_⟩
  intro y
  apply (adelicPointEquiv K L S X h hsep hft hWsep hWft).injective
  rw [Equiv.apply_symm_apply]
  change _ = adelicEvaluation K L S X h
    (RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom (e.symm (g y)))
  rw [adelicEvaluation_stage K L S T X h hsep hft hWsep hWft]
  change _ = numberFieldSpaceStageMap L (numberFieldExceptionalPreimage (L := L) S) X
    (upperLevel K L S T) (e (e.symm (g y)))
  rw [e.apply_symm_apply]
  exact (AdelicSpacePointsProof.numberField_stageMap_transition L
    (numberFieldExceptionalPreimage (L := L) S) (X := X)
    (numberFieldLevelCover_spec K L S U) y).symm

/-- Full adelic points of an original separated finite-type space Weil model are homeomorphic. -/
def adelicPointHomeomorph :
    @Homeomorph
      (NumberFieldSpaceAdelePoints K S
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
      (NumberFieldSpaceAdelePoints L (numberFieldExceptionalPreimage (L := L) S) X)
      (numberFieldSpaceAdelePointTopology K S _)
      (numberFieldSpaceAdelePointTopology L (numberFieldExceptionalPreimage (L := L) S) X) :=
  homeomorphOfStageLifts _ _ (adelicPointEquiv K L S X h hsep hft hWsep hWft)
    (forward_stage_lifts K L S X h hsep hft hWsep hWft)
    (backward_stage_lifts K L S X h hsep hft hWsep hWft)

/-- The assembled homeomorphism has the original counit evaluation as its forward map. -/
@[simp]
theorem adelicPointHomeomorph_apply
    (x : NumberFieldSpaceAdelePoints K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)) :
    adelicPointHomeomorph K L S X h hsep hft hWsep hWft x =
      adelicEvaluation K L S X h x := rfl

end Langlands.Global.NumberFieldSpaceFixedModelWeilHomeomorph

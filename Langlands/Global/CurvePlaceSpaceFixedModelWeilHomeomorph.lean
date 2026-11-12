import Langlands.Global.CurvePlaceSpaceFixedModelWeilEvaluation
import Langlands.Global.AdelicWeilLevelCofinality
import Langlands.Global.AdelicSpacePointTopologyTheorem
import Langlands.Topology.FinalStageComparison

/-! # Full adelic homeomorphism for an original curve-place space Weil model -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers

namespace Langlands.Global.CurvePlaceSpaceFixedModelWeilHomeomorph

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open CurvePlacePrincipalSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup (upperLevel adelicLevelPointHomeomorph)
open CurvePlaceSpaceFixedModelWeilEvaluation AdelicWeilLevelCofinality
open AdelicSpacePointStagesProof AdelicSpacePointTopologyProof Langlands.Topology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients k K L s t))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients k K s t) (upperCoefficients k K L s t)).obj X.toSheaf))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients k K L s t) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients k K s t)
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  (hS : (curvePlacePrincipalExceptional k K s (t : K)).Nonempty)

local instance lowerStageTopology (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K))) :
    TopologicalSpace (RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :=
  curvePlaceSpaceStageTopology k K (curvePlacePrincipalExceptional k K s (t : K)) _ T

local instance upperStageTopology
    (U : AdelicLevelIndexAbove (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) :
    TopologicalSpace (RingPoints (upperCoefficients k K L s t) X
      (curvePlaceAdeleLevelOver k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) U)) :=
  curvePlaceSpaceStageTopology k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X U

include hsep hft hWsep hWft hS

/-- The original full counit evaluation is injective. -/
theorem adelicEvaluation_injective :
    Function.Injective (adelicEvaluation k K L s t X h) := by
  intro a b hab
  obtain ⟨T, x, rfl⟩ := curve_cover spaceFilteredRingPointComparison k K (curvePlacePrincipalExceptional k K s (t : K)) hWft a
  obtain ⟨U, y, rfl⟩ := curve_cover spaceFilteredRingPointComparison k K (curvePlacePrincipalExceptional k K s (t : K)) hWft b
  obtain ⟨V, hTV, hUV⟩ := exists_ge_ge T U
  let xV := RingPoints.changeRing (curvePlaceAdeleLevelOverMap k K (curvePlacePrincipalExceptional k K s (t : K)) hTV).hom x
  let yV := RingPoints.changeRing (curvePlaceAdeleLevelOverMap k K (curvePlacePrincipalExceptional k K s (t : K)) hUV).hom y
  have hx : curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K)) _ V xV = curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K)) _ T x :=
    AdelicSpacePointsProof.curve_stageMap_transition k K (curvePlacePrincipalExceptional k K s (t : K)) hTV x
  have hy : curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K)) _ V yV = curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K)) _ U y :=
    AdelicSpacePointsProof.curve_stageMap_transition k K (curvePlacePrincipalExceptional k K s (t : K)) hUV y
  rw [← hx, ← hy] at hab ⊢
  apply congrArg (curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K)) _ V)
  apply (adelicLevelPointHomeomorph k K L s t V X h hsep hft hWsep hWft hS).injective
  apply RelativeIntegralPoints.changeRing_injective hsep
    (curvePlaceAdeleLevelOverι k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      (upperLevel k K L s t V)).hom (fun _ _ he => Subtype.ext he)
  exact (adelicEvaluation_stage k K L s t V X h hsep hft hWsep hWft hS xV).symm.trans
    (hab.trans (adelicEvaluation_stage k K L s t V X h hsep hft hWsep hWft hS yV))

/-- Cofinal original upper stages are all in the image of the full counit evaluation. -/
theorem adelicEvaluation_surjective :
    Function.Surjective (adelicEvaluation k K L s t X h) := by
  intro b
  obtain ⟨U, y, rfl⟩ := curve_cover spaceFilteredRingPointComparison k L
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) hft b
  let T := curveLevelCover k K L s t U
  let e := adelicLevelPointHomeomorph k K L s t T X h hsep hft hWsep hWft hS
  let yV := RingPoints.changeRing
    (curvePlaceAdeleLevelOverMap k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      (curveLevelCover_spec k K L s t U)).hom y
  refine ⟨curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K)) _ T (e.symm yV), ?_⟩
  change adelicEvaluation k K L s t X h
    (RingPoints.changeRing (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom (e.symm yV)) = _
  rw [adelicEvaluation_stage k K L s t T X h hsep hft hWsep hWft hS]
  change curvePlaceSpaceStageMap k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X
    (upperLevel k K L s t T) (e (e.symm yV)) = _
  rw [e.apply_symm_apply]
  exact AdelicSpacePointsProof.curve_stageMap_transition k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
    (curveLevelCover_spec k K L s t U) y

/-- The original counit is an equivalence on full integral-model adelic points. -/
def adelicPointEquiv :
    CurvePlaceSpaceAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) ≃
      CurvePlaceSpaceAdelePoints k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X :=
  Equiv.ofBijective (adelicEvaluation k K L s t X h)
    ⟨adelicEvaluation_injective k K L s t X h hsep hft hWsep hWft hS,
      adelicEvaluation_surjective k K L s t X h hsep hft hWsep hWft hS⟩

/-- Every lower stage has the original continuous Weil comparison as a full-evaluation lift. -/
theorem forward_stage_lifts :
    HasContinuousStageLifts (curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
      (curvePlaceSpaceStageMap k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X)
      (adelicPointEquiv k K L s t X h hsep hft hWsep hWft hS) := by
  intro T
  exact ⟨upperLevel k K L s t T, adelicLevelPointHomeomorph k K L s t T X h hsep hft hWsep hWft hS,
    (adelicLevelPointHomeomorph k K L s t T X h hsep hft hWsep hWft hS).continuous,
    adelicEvaluation_stage k K L s t T X h hsep hft hWsep hWft hS⟩

/-- Each upper stage lifts continuously through a cofinal full-preimage stage and its inverse. -/
theorem backward_stage_lifts :
    HasContinuousStageLifts
      (curvePlaceSpaceStageMap k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X)
      (curvePlaceSpaceStageMap k K (curvePlacePrincipalExceptional k K s (t : K))
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
      (adelicPointEquiv k K L s t X h hsep hft hWsep hWft hS).symm := by
  intro U
  let T := curveLevelCover k K L s t U
  let e := adelicLevelPointHomeomorph k K L s t T X h hsep hft hWsep hWft hS
  let g := RingPoints.changeRing (X := X)
    (curvePlaceAdeleLevelOverMap k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      (curveLevelCover_spec k K L s t U)).hom
  refine ⟨T, e.symm ∘ g, e.symm.continuous.comp
    (curve_stage_transition k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
      hsep (CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup.upperSupport_nonempty k K L s t hS)
      hft (curveLevelCover_spec k K L s t U)).continuous, ?_⟩
  intro y
  apply (adelicPointEquiv k K L s t X h hsep hft hWsep hWft hS).injective
  rw [Equiv.apply_symm_apply]
  change _ = adelicEvaluation k K L s t X h
    (RingPoints.changeRing (curvePlaceAdeleLevelOverι k K (curvePlacePrincipalExceptional k K s (t : K)) T).hom (e.symm (g y)))
  rw [adelicEvaluation_stage k K L s t T X h hsep hft hWsep hWft hS]
  change _ = curvePlaceSpaceStageMap k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X
    (upperLevel k K L s t T) (e (e.symm (g y)))
  rw [e.apply_symm_apply]
  exact (AdelicSpacePointsProof.curve_stageMap_transition k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))
    (curveLevelCover_spec k K L s t U) y).symm

/-- Full adelic points of an original separated finite-type space Weil model are homeomorphic. -/
def adelicPointHomeomorph :
    @Homeomorph
      (CurvePlaceSpaceAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
      (CurvePlaceSpaceAdelePoints k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X)
      (curvePlaceSpaceAdelePointTopology k K (curvePlacePrincipalExceptional k K s (t : K)) _)
      (curvePlaceSpaceAdelePointTopology k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))) X) :=
  homeomorphOfStageLifts _ _ (adelicPointEquiv k K L s t X h hsep hft hWsep hWft hS)
    (forward_stage_lifts k K L s t X h hsep hft hWsep hWft hS)
    (backward_stage_lifts k K L s t X h hsep hft hWsep hWft hS)

/-- The assembled homeomorphism has the original counit evaluation as its forward map. -/
@[simp]
theorem adelicPointHomeomorph_apply
    (x : CurvePlaceSpaceAdelePoints k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)) :
    adelicPointHomeomorph k K L s t X h hsep hft hWsep hWft hS x =
      adelicEvaluation k K L s t X h x := rfl

end Langlands.Global.CurvePlaceSpaceFixedModelWeilHomeomorph

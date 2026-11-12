import Langlands.Global.AdelicSpaceLevelSecondCountable

/-!
# Topology of adelic points of separated algebraic spaces, given the covering by levels

Conrad, printed p.17: for a separated algebraic space of finite type over the `S`-integers of
a global field, the adelic points are locally compact, Hausdorff and second countable. This
module derives these properties from one input: every adelic point comes from a level. The
stage maps are open embeddings (`AdelicSpacePointStagesProof`), and every stage is locally
compact, Hausdorff and second countable. Any two adelic points lie in a common stage because
the stages are directed, and there are countably many stages.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps

namespace Langlands.Global

namespace AdelicSpacePointsProof

open AdelicSpaceLevelTopologyProof AdelicSpacePointMapsProof AdelicSpacePointStagesProof

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  {X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- The stage maps are compatible with the changes of stage. -/
theorem numberField_stageMap_transition {T T' : AdelicLevelIndexAbove S} (h : T ≤ T')
    (x : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    numberFieldSpaceStageMap K S X T' (RingPoints.changeRing (numberFieldAdeleLevelOverMap K S h).hom x) =
      numberFieldSpaceStageMap K S X T x := by
  simp only [numberFieldSpaceStageMap, ProductPointsDescent.changeRing_changeRing]
  rfl

/-- Every stage is locally compact and Hausdorff. -/
theorem numberField_stage_locallyCompact_t2 (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (T : AdelicLevelIndexAbove S) :
    @LocallyCompactSpace _ (numberFieldSpaceStageTopology K S X T) ∧
      @T2Space _ (numberFieldSpaceStageTopology K S X T) := by
  obtain ⟨hlc, ht2⟩ := numberField_locallyCompact_t2 K T.val
    (X := numberFieldSpaceLevelBaseChange K T.property X) hX.baseChange
    (finiteTypeOverRing_baseChange _ hft)
  have h := numberField_stageEquiv_isHomeomorph K S (X := X) T
  let _ := numberFieldSpaceStageTopology K S X T
  let _ := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)
  exact ⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.t2Space⟩

/-- **Locally compact, Hausdorff and second countable**, number fields, given that every adelic
point comes from a level. -/
theorem numberField_points_of_cover (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hcover : ∀ x : NumberFieldSpaceAdelePoints K S X, ∃ (T : AdelicLevelIndexAbove S)
      (y : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)),
      numberFieldSpaceStageMap K S X T y = x) :
    @LocallyCompactSpace _ (numberFieldSpaceAdelePointTopology K S X) ∧
      @T2Space _ (numberFieldSpaceAdelePointTopology K S X) ∧
      @SecondCountableTopology _ (numberFieldSpaceAdelePointTopology K S X) := by
  let _ := numberFieldSpaceAdelePointTopology K S X
  let _ (T : AdelicLevelIndexAbove S) := numberFieldSpaceStageTopology K S X T
  have hemb := numberField_stage_isOpenEmbedding K S hX hft
  have hlc : ∀ T, LocallyCompactSpace (RingPoints ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevelOver K S T)) := fun T =>
    (numberField_stage_locallyCompact_t2 K S hX hft T).1
  have ht2 : ∀ T, T2Space (RingPoints ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevelOver K S T)) := fun T =>
    (numberField_stage_locallyCompact_t2 K S hX hft T).2
  have hsc : ∀ T, SecondCountableTopology (RingPoints ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevelOver K S T)) := fun T =>
    AdelicSpaceLevelSecondCountable.numberField_stage K S hX hft T
  have : Countable (FinitePlace K) := finitePlace_countable K
  have : Countable (AdelicLevelIndexAbove S) := inferInstance
  refine ⟨Topology.FinalStage.locallyCompactSpace_of_stages _ hemb hcover,
    Topology.FinalStage.t2Space_of_stages _ hemb fun z₁ z₂ => ?_,
    Topology.FinalStage.secondCountableTopology_of_stages _ hemb hcover⟩
  obtain ⟨T₁, a, rfl⟩ := hcover z₁
  obtain ⟨T₂, b, rfl⟩ := hcover z₂
  obtain ⟨T, h₁, h₂⟩ := (isDirected_levelIndex S).directed T₁ T₂
  exact ⟨T, _, _, numberField_stageMap_transition K S h₁ a,
    numberField_stageMap_transition K S h₂ b⟩

end NumberField

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] (S : Finset (AlgebraicCurve.Place k F))
  {X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- The stage maps are compatible with the changes of stage. -/
theorem curve_stageMap_transition {T T' : AdelicLevelIndexAbove S} (h : T ≤ T')
    (x : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    curvePlaceSpaceStageMap k F S X T' (RingPoints.changeRing (curvePlaceAdeleLevelOverMap k F S h).hom x) =
      curvePlaceSpaceStageMap k F S X T x := by
  simp only [curvePlaceSpaceStageMap, ProductPointsDescent.changeRing_changeRing]
  rfl

/-- Every stage is locally compact and Hausdorff. -/
theorem curve_stage_locallyCompact_t2 (hS : S.Nonempty) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (T : AdelicLevelIndexAbove S) :
    @LocallyCompactSpace _ (curvePlaceSpaceStageTopology k F S X T) ∧
      @T2Space _ (curvePlaceSpaceStageTopology k F S X T) := by
  obtain ⟨hlc, ht2⟩ := curve_locallyCompact_t2 k F T.val
    (X := curvePlaceSpaceLevelBaseChange k F T.property X) (hS.mono T.property) hX.baseChange
    (finiteTypeOverRing_baseChange _ hft)
  have h := curve_stageEquiv_isHomeomorph k F S (X := X) T
  let _ := curvePlaceSpaceStageTopology k F S X T
  let _ := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)
  exact ⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.t2Space⟩

/-- **Locally compact, Hausdorff and second countable**, global function fields, given that every adelic
point comes from a level. -/
theorem curve_points_of_cover (hS : S.Nonempty) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hcover : ∀ x : CurvePlaceSpaceAdelePoints k F S X, ∃ (T : AdelicLevelIndexAbove S)
      (y : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)),
      curvePlaceSpaceStageMap k F S X T y = x) :
    @LocallyCompactSpace _ (curvePlaceSpaceAdelePointTopology k F S X) ∧
      @T2Space _ (curvePlaceSpaceAdelePointTopology k F S X) ∧
      @SecondCountableTopology _ (curvePlaceSpaceAdelePointTopology k F S X) := by
  let _ := curvePlaceSpaceAdelePointTopology k F S X
  let _ (T : AdelicLevelIndexAbove S) := curvePlaceSpaceStageTopology k F S X T
  have hemb := curve_stage_isOpenEmbedding k F S hX hS hft
  have hlc : ∀ T, LocallyCompactSpace (RingPoints (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevelOver k F S T)) := fun T =>
    (curve_stage_locallyCompact_t2 k F S hS hX hft T).1
  have ht2 : ∀ T, T2Space (RingPoints (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevelOver k F S T)) := fun T =>
    (curve_stage_locallyCompact_t2 k F S hS hX hft T).2
  have hsc : ∀ T, SecondCountableTopology (RingPoints (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevelOver k F S T)) := fun T =>
    AdelicSpaceLevelSecondCountable.curve_stage k F S hX hft T
  have : Countable (AlgebraicCurve.Place k F) := curvePlace_countable k F
  have : Countable (AdelicLevelIndexAbove S) := inferInstance
  refine ⟨Topology.FinalStage.locallyCompactSpace_of_stages _ hemb hcover,
    Topology.FinalStage.t2Space_of_stages _ hemb fun z₁ z₂ => ?_,
    Topology.FinalStage.secondCountableTopology_of_stages _ hemb hcover⟩
  obtain ⟨T₁, a, rfl⟩ := hcover z₁
  obtain ⟨T₂, b, rfl⟩ := hcover z₂
  obtain ⟨T, h₁, h₂⟩ := (isDirected_levelIndex S).directed T₁ T₂
  exact ⟨T, _, _, curve_stageMap_transition k F S h₁ a,
    curve_stageMap_transition k F S h₂ b⟩

end Curve

end AdelicSpacePointsProof

end Langlands.Global

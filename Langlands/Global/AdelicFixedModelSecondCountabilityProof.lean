import Langlands.Global.AdelicFixedModelSecondCountabilityStatement
import Langlands.Global.AdelicFixedModelAlgebraColimitProof
import Langlands.Global.AdelicFixedModelTransitionTopologyProof
import Langlands.Global.AdelicLevelModelSecondCountabilityProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointTopologicalProof

/-! # Second countability of actual full-adele model points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

private theorem curvePlaceFixedModelStage_secondCountableTopology
    (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (T : AdelicLevelIndexAbove S) :
    @SecondCountableTopology _ (curvePlaceFixedModelStageTopology k F S X T) := by
  let XT := curvePlaceLevelModelBaseChange k F T.property X
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceLevelModelPointTopology k F T.val XT
  let := adelicLevelModelSecondCountability.1 k F T.val XT
  exact (curvePlaceFixedModelPointHomeomorph k F S X T).secondCountableTopology

private theorem numberFieldFixedModelStage_secondCountableTopology
    (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (T : AdelicLevelIndexAbove S) :
    @SecondCountableTopology _ (numberFieldFixedModelStageTopology K S X T) := by
  let XT := numberFieldLevelModelBaseChange K T.property X
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldLevelModelPointTopology K T.val XT
  let := adelicLevelModelSecondCountability.2 K T.val XT
  exact (numberFieldFixedModelPointHomeomorph K S X T).secondCountableTopology

/-- Countably many open, second-countable arithmetic stages cover the actual
full-adele model points in their final topology. -/
theorem adelicFixedModelSecondCountability :
    AdelicFixedModelSecondCountabilityStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S X _ _
    let : Countable (AlgebraicCurve.Place k F) := curvePlace_countable k F
    let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
      (adelicSIntegersNoetherian.1 k F S).1
    have hfp : LocallyOfFinitePresentation X.hom := inferInstance
    have hcover := ((filteredRingPointComparison
      (curvePlaceSIntegers k F S) (AdelicLevelIndexAbove S)
      (curvePlaceAdeleLevelOverDiagram k F S) (curvePlaceAdeleOverCocone k F S)
      (curvePlaceAdeleOverIsColimit k F S) X).2 hfp).1
    have h := (filteredRingPointTopologicalComparison
      (curvePlaceSIntegers k F S) (AdelicLevelIndexAbove S)
      (curvePlaceAdeleLevelOverDiagram k F S) (curvePlaceAdeleOverCocone k F S)
      (curvePlaceAdeleOverIsColimit k F S) X hfp
      (curvePlaceFixedModelStageTopology k F S X)).2
        (fun T U f => by
          have hTU := adelicFixedModelTransitionTopology.1 k F S X T U (leOfHom f)
          exact ⟨hTU.1, hTU.2.1⟩)
    apply h.2.2.1 Set.univ (Set.to_countable _)
    · intro p
      obtain ⟨T, q, hq⟩ := hcover p
      exact ⟨T, Set.mem_univ _, q, hq⟩
    · intro T _
      exact curvePlaceFixedModelStage_secondCountableTopology k F S X T
  · intro K _ _ S X _ _
    let : Countable (FinitePlace K) := finitePlace_countable K
    let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
      (adelicSIntegersNoetherian.2 K S).1
    have hfp : LocallyOfFinitePresentation X.hom := inferInstance
    have hcover := ((filteredRingPointComparison
      ((S : Set (FinitePlace K)).integer K) (AdelicLevelIndexAbove S)
      (numberFieldAdeleLevelOverDiagram K S) (numberFieldAdeleOverCocone K S)
      (numberFieldAdeleOverIsColimit K S) X).2 hfp).1
    have h := (filteredRingPointTopologicalComparison
      ((S : Set (FinitePlace K)).integer K) (AdelicLevelIndexAbove S)
      (numberFieldAdeleLevelOverDiagram K S) (numberFieldAdeleOverCocone K S)
      (numberFieldAdeleOverIsColimit K S) X hfp
      (numberFieldFixedModelStageTopology K S X)).2
        (fun T U f => by
          have hTU := adelicFixedModelTransitionTopology.2 K S X T U (leOfHom f)
          exact ⟨hTU.1, hTU.2.1⟩)
    apply h.2.2.1 Set.univ (Set.to_countable _)
    · intro p
      obtain ⟨T, q, hq⟩ := hcover p
      exact ⟨T, Set.mem_univ _, q, hq⟩
    · intro T _
      exact numberFieldFixedModelStage_secondCountableTopology K S X T

end Langlands.Global

import Langlands.Global.AdelicFixedModelLocalCompactnessStatement
import Langlands.Global.AdelicFixedModelAlgebraColimitProof
import Langlands.Global.AdelicFixedModelTransitionTopologyProof
import Langlands.Global.AdelicLevelModelLocalCompactnessProof
import Langlands.Global.AdelicSIntegersNoetherianProof
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointTopologicalProof

/-! # Local compactness of actual full-adele model points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

private theorem curvePlaceFixedModelStageProperties
    (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F))
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (T : AdelicLevelIndexAbove S) :
    @LocallyCompactSpace _ (curvePlaceFixedModelStageTopology k F S X T) ∧
      (∀ [IsSeparated X.hom],
        @T2Space _ (curvePlaceFixedModelStageTopology k F S X T)) := by
  let XT := curvePlaceLevelModelBaseChange k F T.property X
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceLevelModelPointTopology k F T.val XT
  have h := adelicLevelModelLocalCompactness.1 k F T.val XT
  refine ⟨(curvePlaceFixedModelPointHomeomorph k F S X T).locallyCompactSpace_iff.mpr
    h.1, ?_⟩
  intro hSep
  let : IsSeparated XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let := h.2
  exact (curvePlaceFixedModelPointHomeomorph k F S X T).isEmbedding.t2Space

private theorem numberFieldFixedModelStageProperties
    (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (T : AdelicLevelIndexAbove S) :
    @LocallyCompactSpace _ (numberFieldFixedModelStageTopology K S X T) ∧
      (∀ [IsSeparated X.hom],
        @T2Space _ (numberFieldFixedModelStageTopology K S X T)) := by
  let XT := numberFieldLevelModelBaseChange K T.property X
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldLevelModelPointTopology K T.val XT
  have h := adelicLevelModelLocalCompactness.2 K T.val XT
  refine ⟨(numberFieldFixedModelPointHomeomorph K S X T).locallyCompactSpace_iff.mpr
    h.1, ?_⟩
  intro hSep
  let : IsSeparated XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let := h.2
  exact (numberFieldFixedModelPointHomeomorph K S X T).isEmbedding.t2Space

/-- The arithmetic stages supply local compactness and conditional Hausdorffness
of actual full-adele points, with precisely their final topology. -/
theorem adelicFixedModelLocalCompactness :
    AdelicFixedModelLocalCompactnessStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S X _ _
    let : IsNoetherianRing (curvePlaceSIntegers k F S) :=
      (adelicSIntegersNoetherian.1 k F S).1
    have hfp : LocallyOfFinitePresentation X.hom := inferInstance
    have h := (filteredRingPointTopologicalComparison
      (curvePlaceSIntegers k F S) (AdelicLevelIndexAbove S)
      (curvePlaceAdeleLevelOverDiagram k F S) (curvePlaceAdeleOverCocone k F S)
      (curvePlaceAdeleOverIsColimit k F S) X hfp
      (curvePlaceFixedModelStageTopology k F S X)).2
        (fun T U f => by
          have hTU := adelicFixedModelTransitionTopology.1 k F S X T U (leOfHom f)
          exact ⟨hTU.1, hTU.2.1⟩)
    refine ⟨h.2.1 (fun T => (curvePlaceFixedModelStageProperties k F S X T).1), ?_⟩
    intro hSep
    exact (h.2.2.2 (fun T U f => by
      let := curvePlaceFixedModelStageTopology k F S X T
      let := curvePlaceFixedModelStageTopology k F S X U
      exact (adelicFixedModelTransitionTopology.1 k F S X T U (leOfHom f)).2.2.injective)).2
        (fun T => (curvePlaceFixedModelStageProperties k F S X T).2)
  · intro K _ _ S X _ _
    let : IsNoetherianRing ((S : Set (FinitePlace K)).integer K) :=
      (adelicSIntegersNoetherian.2 K S).1
    have hfp : LocallyOfFinitePresentation X.hom := inferInstance
    have h := (filteredRingPointTopologicalComparison
      ((S : Set (FinitePlace K)).integer K) (AdelicLevelIndexAbove S)
      (numberFieldAdeleLevelOverDiagram K S) (numberFieldAdeleOverCocone K S)
      (numberFieldAdeleOverIsColimit K S) X hfp
      (numberFieldFixedModelStageTopology K S X)).2
        (fun T U f => by
          have hTU := adelicFixedModelTransitionTopology.2 K S X T U (leOfHom f)
          exact ⟨hTU.1, hTU.2.1⟩)
    refine ⟨h.2.1 (fun T => (numberFieldFixedModelStageProperties K S X T).1), ?_⟩
    intro hSep
    exact (h.2.2.2 (fun T U f => by
      let := numberFieldFixedModelStageTopology K S X T
      let := numberFieldFixedModelStageTopology K S X U
      exact (adelicFixedModelTransitionTopology.2 K S X T U (leOfHom f)).2.2.injective)).2
        (fun T => (numberFieldFixedModelStageProperties K S X T).2)

end Langlands.Global

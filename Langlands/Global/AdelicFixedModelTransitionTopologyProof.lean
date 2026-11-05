import Langlands.Global.AdelicFixedModelTransitionTopologyStatement
import Langlands.Global.AdelicFixedModelTransition
import Langlands.Global.AdelicLevelModelTransitionTopologyProof
import Langlands.Global.AdelicLevelModelFunctorialityProof

/-! # Topology of actual fixed-base arithmetic coefficient changes -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Actual curve-model isomorphisms give homeomorphisms on arithmetic stage points. -/
def curvePlaceLevelModelIsoHomeomorph
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F))
    {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))} (e : X ≅ Y) :
    @Homeomorph
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevel k F S))
      (curvePlaceLevelModelPointTopology k F S X)
      (curvePlaceLevelModelPointTopology k F S Y) := by
  letI := curvePlaceLevelModelPointTopology k F S X
  letI := curvePlaceLevelModelPointTopology k F S Y
  exact {
    toFun := fun p => p ≫ e.hom
    invFun := fun p => p ≫ e.inv
    left_inv := fun p => (Category.assoc p e.hom e.inv).trans
      ((congrArg (fun f => p ≫ f) e.hom_inv_id).trans (Category.comp_id p))
    right_inv := fun p => (Category.assoc p e.inv e.hom).trans
      ((congrArg (fun f => p ≫ f) e.inv_hom_id).trans (Category.comp_id p))
    continuous_toFun := adelicLevelModelFunctoriality.1 k F S X Y e.hom
    continuous_invFun := adelicLevelModelFunctoriality.1 k F S Y X e.inv }

/-- Actual full number-field model isomorphisms act homeomorphically on stage points. -/
def numberFieldLevelModelIsoHomeomorph
    (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
    {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    (e : X ≅ Y) :
    @Homeomorph
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevel K S))
      (numberFieldLevelModelPointTopology K S X)
      (numberFieldLevelModelPointTopology K S Y) := by
  letI := numberFieldLevelModelPointTopology K S X
  letI := numberFieldLevelModelPointTopology K S Y
  exact {
    toFun := fun p => p ≫ e.hom
    invFun := fun p => p ≫ e.inv
    left_inv := fun p => (Category.assoc p e.hom e.inv).trans
      ((congrArg (fun f => p ≫ f) e.hom_inv_id).trans (Category.comp_id p))
    right_inv := fun p => (Category.assoc p e.inv e.hom).trans
      ((congrArg (fun f => p ≫ f) e.inv_hom_id).trans (Category.comp_id p))
    continuous_toFun := adelicLevelModelFunctoriality.2 K S X Y e.hom
    continuous_invFun := adelicLevelModelFunctoriality.2 K S Y X e.inv }

/-- The literal fixed-base function-field coefficient maps have the original topology. -/
theorem curvePlaceFixedModelTransitionTopology :
    CurvePlaceFixedModelTransitionTopologyStatement.{u} := by
  intro k F _ _ _ _ _ _ S X _ _ T U hTU
  let XT := curvePlaceLevelModelBaseChange k F T.property X
  let XTU := curvePlaceLevelModelBaseChange k F hTU XT
  let XU := curvePlaceLevelModelBaseChange k F U.property X
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceFixedModelStageTopology k F S X U
  let := curvePlaceLevelModelPointTopology k F T.val XT
  let := curvePlaceLevelModelPointTopology k F U.val XTU
  let := curvePlaceLevelModelPointTopology k F U.val XU
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  let source := curvePlaceFixedModelPointHomeomorph k F S X T
  let target :=
    (curvePlaceLevelModelIsoHomeomorph k F U.val
      (curvePlaceFixedModelPullbackCompIso k F S X hTU)).trans
        (curvePlaceFixedModelPointHomeomorph k F S X U).symm
  let transition := curvePlaceLevelModelTransition k F hTU XT
  have h := adelicLevelModelTransitionTopology.1 k F T.val U.val hTU XT
  have hn : (fun p => target (transition (source p))) =
      RingPoint.changeRing (curvePlaceAdeleLevelOverMap k F S hTU).hom (X := X) := by
    funext p
    exact curvePlaceFixedModelTransition_natural k F S X hTU p
  have hc := target.continuous.comp (h.1.comp source.continuous)
  change Continuous (fun p => target (transition (source p))) at hc
  rw [hn] at hc
  have ho := target.isOpenMap.comp (h.2.1.comp source.isOpenMap)
  change IsOpenMap (fun p => target (transition (source p))) at ho
  rw [hn] at ho
  refine ⟨hc, ho, ?_⟩
  intro hSep
  let : IsSeparated XT.hom := by
    dsimp [XT, curvePlaceLevelModelBaseChange]
    infer_instance
  have he := target.isOpenEmbedding.comp (h.2.2.comp source.isOpenEmbedding)
  change IsOpenEmbedding (fun p => target (transition (source p))) at he
  rwa [hn] at he

/-- The literal fixed-base full number-field coefficient maps have the original topology. -/
theorem numberFieldFixedModelTransitionTopology :
    NumberFieldFixedModelTransitionTopologyStatement.{u} := by
  intro K _ _ S X _ _ T U hTU
  let XT := numberFieldLevelModelBaseChange K T.property X
  let XTU := numberFieldLevelModelBaseChange K hTU XT
  let XU := numberFieldLevelModelBaseChange K U.property X
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldFixedModelStageTopology K S X U
  let := numberFieldLevelModelPointTopology K T.val XT
  let := numberFieldLevelModelPointTopology K U.val XTU
  let := numberFieldLevelModelPointTopology K U.val XU
  let : LocallyOfFiniteType XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  let source := numberFieldFixedModelPointHomeomorph K S X T
  let target :=
    (numberFieldLevelModelIsoHomeomorph K U.val
      (numberFieldFixedModelPullbackCompIso K S X hTU)).trans
        (numberFieldFixedModelPointHomeomorph K S X U).symm
  let transition := numberFieldLevelModelTransition K hTU XT
  have h := adelicLevelModelTransitionTopology.2 K T.val U.val hTU XT
  have hn : (fun p => target (transition (source p))) =
      RingPoint.changeRing (numberFieldAdeleLevelOverMap K S hTU).hom (X := X) := by
    funext p
    exact numberFieldFixedModelTransition_natural K S X hTU p
  have hc := target.continuous.comp (h.1.comp source.continuous)
  change Continuous (fun p => target (transition (source p))) at hc
  rw [hn] at hc
  have ho := target.isOpenMap.comp (h.2.1.comp source.isOpenMap)
  change IsOpenMap (fun p => target (transition (source p))) at ho
  rw [hn] at ho
  refine ⟨hc, ho, ?_⟩
  intro hSep
  let : IsSeparated XT.hom := by
    dsimp [XT, numberFieldLevelModelBaseChange]
    infer_instance
  have he := target.isOpenEmbedding.comp (h.2.2.comp source.isOpenEmbedding)
  change IsOpenEmbedding (fun p => target (transition (source p))) at he
  rwa [hn] at he


/-- The exact fixed-base topology theorem in both arithmetic branches. -/
theorem adelicFixedModelTransitionTopology :
    AdelicFixedModelTransitionTopologyStatement.{u} :=
  ⟨curvePlaceFixedModelTransitionTopology, numberFieldFixedModelTransitionTopology⟩

end Langlands.Global

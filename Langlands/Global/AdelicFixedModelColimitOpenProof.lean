import Langlands.Global.AdelicFixedModelColimitOpenStatement
import Langlands.Global.AdelicFixedModelTransitionTopologyProof
import Langlands.Global.AdelicFixedModelFiniteTypeProof
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointOpenProof

/-! # Open arithmetic stages in actual full-adele model points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The actual function-field comparison transports open stages and their
quotient images to full-adele model points. -/
theorem curvePlaceFixedModelColimitOpen :
    CurvePlaceFixedModelColimitOpenStatement.{u} := by
  intro k F _ _ _ _ _ _ S X _ _
  let R : Type u := curvePlaceSIntegers k F S
  let D := curvePlaceAdeleLevelOverDiagram k F S
  let τ := curvePlaceFixedModelStageTopology k F S X
  let c := curvePlaceAdeleOverCocone k F S
  have hT : ∀ (T U : AdelicLevelIndexAbove S) (f : T ⟶ U),
      Continuous[τ T, τ U]
        (fun p : RingPoint R X (D.obj T) => p.changeRing (D.map f).hom) ∧
      @IsOpenMap _ _ (τ T) (τ U)
        (fun p : RingPoint R X (D.obj T) => p.changeRing (D.map f).hom) := by
    intro T U f
    have h := adelicFixedModelTransitionTopology.1 k F S X T U (leOfHom f)
    exact ⟨h.1, h.2.1⟩
  have ho := filteredRingPointOpenStages R (AdelicLevelIndexAbove S) D X τ hT
  have hb := (adelicFixedModelFiniteType.1 k F S X).2.1
  let := ringPointColimitTopology R D X τ
  let := ringPointCoconeTopology R D X τ c
  let e := ringPointColimitHomeomorph R D X τ c hb
  refine ⟨?_, ?_, ?_⟩
  · intro T
    let : TopologicalSpace (RingPoint R X (D.obj T)) := τ T
    refine ⟨ringPointCoconeTopology_continuous_ι R D X τ c T, ?_⟩
    change IsOpenMap (e ∘ ringPointColimitι R D X T)
    exact e.isOpenMap.comp (ho.1 T)
  · intro T
    let := ringPointColimitStageImageTopology R D X τ T
    change IsOpenEmbedding (e ∘ fun p : RingPointColimitStageImage R D X T => p.val)
    exact e.isOpenEmbedding.comp (ho.2.1 T)
  · intro _ T
    have hinj : ∀ (U V : AdelicLevelIndexAbove S) (f : U ⟶ V),
        Function.Injective
          (fun p : RingPoint R X (D.obj U) => p.changeRing (D.map f).hom) := by
      intro U V f
      exact (adelicFixedModelTransitionTopology.1 k F S X U V (leOfHom f)).2.2.injective
    let : TopologicalSpace (RingPoint R X (D.obj T)) := τ T
    change IsOpenEmbedding (e ∘ ringPointColimitι R D X T)
    exact e.isOpenEmbedding.comp (ho.2.2 hinj T)

/-- The full number-field comparison transports the same open-stage assertions,
retaining all infinite completions. -/
theorem numberFieldFixedModelColimitOpen :
    NumberFieldFixedModelColimitOpenStatement.{u} := by
  intro K _ _ S X _ _
  let R : Type u := (S : Set (FinitePlace K)).integer K
  let D := numberFieldAdeleLevelOverDiagram K S
  let τ := numberFieldFixedModelStageTopology K S X
  let c := numberFieldAdeleOverCocone K S
  have hT : ∀ (T U : AdelicLevelIndexAbove S) (f : T ⟶ U),
      Continuous[τ T, τ U]
        (fun p : RingPoint R X (D.obj T) => p.changeRing (D.map f).hom) ∧
      @IsOpenMap _ _ (τ T) (τ U)
        (fun p : RingPoint R X (D.obj T) => p.changeRing (D.map f).hom) := by
    intro T U f
    have h := adelicFixedModelTransitionTopology.2 K S X T U (leOfHom f)
    exact ⟨h.1, h.2.1⟩
  have ho := filteredRingPointOpenStages R (AdelicLevelIndexAbove S) D X τ hT
  have hb := (adelicFixedModelFiniteType.2 K S X).2.1
  let := ringPointColimitTopology R D X τ
  let := ringPointCoconeTopology R D X τ c
  let e := ringPointColimitHomeomorph R D X τ c hb
  refine ⟨?_, ?_, ?_⟩
  · intro T
    let : TopologicalSpace (RingPoint R X (D.obj T)) := τ T
    refine ⟨ringPointCoconeTopology_continuous_ι R D X τ c T, ?_⟩
    change IsOpenMap (e ∘ ringPointColimitι R D X T)
    exact e.isOpenMap.comp (ho.1 T)
  · intro T
    let := ringPointColimitStageImageTopology R D X τ T
    change IsOpenEmbedding (e ∘ fun p : RingPointColimitStageImage R D X T => p.val)
    exact e.isOpenEmbedding.comp (ho.2.1 T)
  · intro _ T
    have hinj : ∀ (U V : AdelicLevelIndexAbove S) (f : U ⟶ V),
        Function.Injective
          (fun p : RingPoint R X (D.obj U) => p.changeRing (D.map f).hom) := by
      intro U V f
      exact (adelicFixedModelTransitionTopology.2 K S X U V (leOfHom f)).2.2.injective
    let : TopologicalSpace (RingPoint R X (D.obj T)) := τ T
    change IsOpenEmbedding (e ∘ ringPointColimitι R D X T)
    exact e.isOpenEmbedding.comp (ho.2.2 hinj T)

/-- The exact arithmetic open-stage target in both global-field characteristics. -/
theorem adelicFixedModelColimitOpen : AdelicFixedModelColimitOpenStatement.{u} :=
  ⟨curvePlaceFixedModelColimitOpen, numberFieldFixedModelColimitOpen⟩

end Langlands.Global

import Langlands.Global.AdelicFixedModelPointComparisonStatement
import Langlands.Global.AdelicFixedModelAlgebraColimitProof
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointProof

/-! # Proof of the actual fixed-model adelic point comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Specialize the actual scheme-point comparison and its final-topology upgrade. -/
theorem curvePlaceFixedModelPointComparisonProperties :
    curvePlaceFixedModelPointComparisonStatement.{u} := by
  intro k F _ _ _ S X
  have h := filteredRingPointComparison (curvePlaceSIntegers k F S) (AdelicLevelIndexAbove S)
    (curvePlaceAdeleLevelOverDiagram k F S) (curvePlaceAdeleOverCocone k F S)
    (curvePlaceAdeleOverIsColimit k F S) X
  constructor
  · intro hft
    obtain ⟨hinj, heq, heq'⟩ := h.1 hft
    refine ⟨hinj, ?_, ?_⟩
    · intro T U p q
      constructor
      · intro hpq
        obtain ⟨V, f, g, hfg⟩ := (heq T U p q).mp hpq
        exact ⟨V, leOfHom f, leOfHom g, hfg⟩
      · rintro ⟨V, hTV, hUV, hpq⟩
        exact (heq T U p q).mpr ⟨V, homOfLE hTV, homOfLE hUV, hpq⟩
    · intro T p q
      constructor
      · intro hpq
        obtain ⟨V, f, hf⟩ := (heq' T p q).mp hpq
        exact ⟨V, leOfHom f, hf⟩
      · rintro ⟨V, hTV, hpq⟩
        exact (heq' T p q).mpr ⟨V, homOfLE hTV, hpq⟩
  · intro hfp
    obtain ⟨hstage, _, hbij⟩ := h.2 hfp
    refine ⟨hstage, hbij, ?_⟩
    exact @Homeomorph.isHomeomorph _ _
      (ringPointColimitTopology (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOverDiagram k F S) X
        (curvePlaceFixedModelStageTopology k F S X))
      (ringPointCoconeTopology (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOverDiagram k F S) X
        (curvePlaceFixedModelStageTopology k F S X) (curvePlaceAdeleOverCocone k F S))
      (ringPointColimitHomeomorph (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOverDiagram k F S) X
        (curvePlaceFixedModelStageTopology k F S X) (curvePlaceAdeleOverCocone k F S) hbij)

/-- Specialize the actual scheme-point comparison and its final-topology upgrade. -/
theorem numberFieldFixedModelPointComparisonProperties :
    numberFieldFixedModelPointComparisonStatement.{u} := by
  intro K _ _ S X
  have h := filteredRingPointComparison ((S : Set (FinitePlace K)).integer K) (AdelicLevelIndexAbove S)
    (numberFieldAdeleLevelOverDiagram K S) (numberFieldAdeleOverCocone K S)
    (numberFieldAdeleOverIsColimit K S) X
  constructor
  · intro hft
    obtain ⟨hinj, heq, heq'⟩ := h.1 hft
    refine ⟨hinj, ?_, ?_⟩
    · intro T U p q
      constructor
      · intro hpq
        obtain ⟨V, f, g, hfg⟩ := (heq T U p q).mp hpq
        exact ⟨V, leOfHom f, leOfHom g, hfg⟩
      · rintro ⟨V, hTV, hUV, hpq⟩
        exact (heq T U p q).mpr ⟨V, homOfLE hTV, homOfLE hUV, hpq⟩
    · intro T p q
      constructor
      · intro hpq
        obtain ⟨V, f, hf⟩ := (heq' T p q).mp hpq
        exact ⟨V, leOfHom f, hf⟩
      · rintro ⟨V, hTV, hpq⟩
        exact (heq' T p q).mpr ⟨V, homOfLE hTV, hpq⟩
  · intro hfp
    obtain ⟨hstage, _, hbij⟩ := h.2 hfp
    refine ⟨hstage, hbij, ?_⟩
    exact @Homeomorph.isHomeomorph _ _
      (ringPointColimitTopology ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOverDiagram K S) X
        (numberFieldFixedModelStageTopology K S X))
      (ringPointCoconeTopology ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOverDiagram K S) X
        (numberFieldFixedModelStageTopology K S X) (numberFieldAdeleOverCocone K S))
      (ringPointColimitHomeomorph ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOverDiagram K S) X
        (numberFieldFixedModelStageTopology K S X) (numberFieldAdeleOverCocone K S) hbij)

/-- Both arithmetic branches of the exact fixed-model point target. -/
theorem adelicFixedModelPointComparison : AdelicFixedModelPointComparisonStatement.{u} :=
  ⟨curvePlaceFixedModelPointComparisonProperties, numberFieldFixedModelPointComparisonProperties⟩

end Langlands.Global

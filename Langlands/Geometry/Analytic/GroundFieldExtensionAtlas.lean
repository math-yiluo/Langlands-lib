import Langlands.Geometry.Analytic.GroundFieldExtensionChartSystem
import Langlands.Geometry.Analytic.AffinoidChartLiftTopology
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionSurjectiveProof

/-! # The affinoid atlas after extension of the ground field -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The glued projection sends each new chart onto its original chart. -/
theorem projection_image_chart (i : a.Index) :
    projection K L a '' range ((chartSystem K L a).chart i) =
      range (a.chart i) := by
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨_, (projection_chart K L a i s).symm⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := spectrumProjection_surjective K L (a.algebra i) s
    exact ⟨_, ⟨t, rfl⟩, by rw [projection_chart, ht]⟩

/-- Scalar extension retains exactly the original chart containments. -/
theorem range_chart_subset_iff (i j : a.Index) :
    range ((chartSystem K L a).chart i) ⊆
      range ((chartSystem K L a).chart j) ↔
        range (a.chart i) ⊆ range (a.chart j) := by
  constructor
  · intro h
    have hi := image_mono (f := projection K L a) h
    simpa only [projection_image_chart K L a] using hi
  · intro h
    rw [range_chart, range_chart]
    exact preimage_mono h

/-- Original chart indices still give distinct chart domains after extension. -/
theorem chartDomain_injective :
    Function.Injective (fun i : a.Index => range ((chartSystem K L a).chart i)) := by
  intro i j h
  apply a.chartDomain_injective
  exact ((range_chart_subset_iff K L a i j).1 h.subset).antisymm
    ((range_chart_subset_iff K L a j i).1 h.symm.subset)

/-- The full indexed atlas on the actual glued scalar extension. -/
def atlas : IndexedAffinoidAtlas.{u', max u' w, w} L (chartSystem K L a).Space where
  Index := a.Index
  algebra := chartAlgebra K L a
  chart := (chartSystem K L a).chart
  isEmbedding_chart :=
    (AffinoidChartSystem.AtlasProjection.topology K L X a (chartSystem K L a)
      (atlasProjection K L a)).1
  chartDomain_injective := chartDomain_injective K L a
  locallyHausdorff :=
    (AffinoidChartSystem.AtlasProjection.topology K L X a (chartSystem K L a)
      (atlasProjection K L a)).2.1
  isNet_chartFamily :=
    (AffinoidChartSystem.AtlasProjection.topology K L X a (chartSystem K L a)
      (atlasProjection K L a)).2.2
  restriction i j h :=
    restriction K L a i j ((range_chart_subset_iff K L a i j).1 h)
  restriction_chart i j h s :=
    (chartSystem K L a).chart_pull
      ((range_chart_subset_iff K L a i j).1 h) s
  restriction_universal i j h R φ hφ := by
    apply (restriction_represents K L a i j
      ((range_chart_subset_iff K L a i j).1 h)).2.2 R φ
    intro x
    have hx := hφ x
    rw [range_chart] at hx
    exact hx
  restriction_id i _ := restriction_refl K L a i
  restriction_comp i j k hij hjk _ :=
    restriction_trans K L a
      ((range_chart_subset_iff K L a i j).1 hij)
      ((range_chart_subset_iff K L a j k).1 hjk)

/-- The corresponding atlas presentation over the extended ground field. -/
def presentation : AffinoidAtlasPresentation.{u', max u' w, w} L where
  space := TopCat.of (chartSystem K L a).Space
  atlas := atlas K L a

/-- The glued projection is surjective, including the empty-atlas case. -/
theorem projection_surjective : Function.Surjective (projection K L a) := by
  intro x
  have hx : x ∈ ⋃₀ range (fun i => range (a.chart i)) := by
    rw [a.isNet_chartFamily.1.covers]
    trivial
  obtain ⟨_, ⟨i, rfl⟩, hx⟩ := hx
  have hx' : x ∈ projection K L a '' range ((chartSystem K L a).chart i) := by
    rw [projection_image_chart K L a]
    exact hx
  obtain ⟨z, hz, hzx⟩ := hx'
  exact ⟨z, hzx⟩

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

import Langlands.Geometry.Analytic.AffinoidChartGluing
import Langlands.Geometry.Analytic.DisjointAffinoidAtlas

/-! # Chartwise projections from quotient chart systems to affinoid atlases -/

noncomputable section

universe u v w u' w'

namespace Langlands.Analytic.AffinoidChartSystem

open Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type u'} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  {X : Type v} [TopologicalSpace X]

/-- Internal data relating an actual quotient chart system to an existing
atlas. The new chart domains are precisely the inverse images of the old
ones. The quotient space itself is always `C.Space`. -/
structure AtlasProjection (C : AffinoidChartSystem.{u', w'} L)
    (a : IndexedAffinoidAtlas.{u, v, w} K X) where
  chartIndex : a.Index ≃ C.Index
  pointMap : C(C.Space, X)
  chartPoint : ∀ i, C(BanachSpectrum (C.algebra (chartIndex i)), BanachSpectrum (a.algebra i))
  pointMap_chart : ∀ i s, pointMap (C.chart (chartIndex i) s) = a.chart i (chartPoint i s)
  range_chart : ∀ i, range (C.chart (chartIndex i)) = pointMap ⁻¹' range (a.chart i)
  sub_of_subset : ∀ i j, range (a.chart i) ⊆ range (a.chart j) →
    C.Sub (chartIndex i) (chartIndex j)

end Langlands.Analytic.AffinoidChartSystem

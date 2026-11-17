import Langlands.Geometry.Analytic.AffinoidChartLift

/-! # Topological laws for a quotient chart system over an affinoid atlas -/

universe u v w u' w'

namespace Langlands.Analytic.AffinoidChartSystem.AtlasProjection

open Set Topology
open scoped Topology

/-- The actual quotient has embedded charts, is locally Hausdorff, and
inherits the original chart net. No global Hausdorffness is required. -/
def TopologyStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (X : Type v) [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, v, w} K X) (C : AffinoidChartSystem.{u', w'} L)
    (P : C.AtlasProjection a),
    (∀ i : a.Index, IsEmbedding (C.chart (P.chartIndex i))) ∧
      (∀ z : C.Space, ∃ U : Set C.Space, U ∈ 𝓝 z ∧ T2Space U) ∧
      AtlasTopology.IsNet (range fun i : a.Index => range (C.chart (P.chartIndex i)))

end Langlands.Analytic.AffinoidChartSystem.AtlasProjection

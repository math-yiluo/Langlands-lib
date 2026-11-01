import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain

/-! # Spectrum embedding for every full affinoid-domain representation -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

/-- Every full affinoid-domain representation embeds its actual spectrum as
the represented closed subspace. The embedding is the stored structural
spectrum map, rather than an independently chosen map. -/
def SpectrumEmbeddingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (U : Domain K A),
    Topology.IsClosedEmbedding U.spectrumMap

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain

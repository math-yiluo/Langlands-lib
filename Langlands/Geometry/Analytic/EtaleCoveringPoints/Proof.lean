import Langlands.Geometry.Analytic.EtaleCoveringPoints.Statement
import Langlands.Geometry.Analytic.EtalePointwiseLifting.Proof

/-! # Ordinary points of analytic étale covering sieves -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Every analytic étale covering sieve is jointly surjective on ordinary points. -/
theorem etaleCoveringPoints : EtaleCoveringPointsStatement.{u, v} K := by
  intro X U S hS
  exact jointlySurjective_of_mem_etaleTopology_of_pointwiseLifting
    (etalePointwiseLifting (K := K)) S hS

end Langlands.Analytic.SaturatedAtlasPresentation

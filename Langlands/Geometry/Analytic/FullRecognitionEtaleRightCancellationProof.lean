import Langlands.Geometry.Analytic.FullRecognitionEtaleRightCancellationStatement
import Langlands.Geometry.Analytic.AffinoidEtalePointCancellation
import Langlands.Geometry.Analytic.FullRecognitionFiniteRightCancellationProof

/-! # Strong étale right cancellation over all affinoid pieces: proof -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

/-- **Étale right cancellation.** For composable strong maps between the saturated
presentations of affinoid atlas presentations over a complete ultrametric field, if the second
map and the composite are étale over all recognized affinoid pieces, so is the first map. -/
theorem etaleRightCancellation (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : EtaleRightCancellationStatement.{u, v, w} K :=
  etaleRightCancellation_of_finiteOver (finiteOverRightCancellation K)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

import Langlands.Geometry.Analytic.EtaleGeometricPointImageTransport
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks
import Langlands.Geometry.Analytic.EtalePointwiseLifting.LocalizedStability
import Langlands.Geometry.Analytic.FullRecognitionFieldPointLifts
import Langlands.Geometry.Analytic.LocalizedEtaleFieldPointPullbackProof
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof

/-! # Geometric points of the analytic étale site -/

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

/-- The fibre functor of a geometric point satisfies the point axioms
for the analytic étale topology. -/
theorem geometricPointStatement : GeometricPointStatement.{u, v, uL} := by
  refine geometricPointStatement_of_etalePullbacks_and_imageLift ?_ ?_
  · intro K _ _ _
    refine ⟨localizedEtaleStability, localizedEtalePullbackBaseChange, ?_⟩
    intro L _ _ _ _ _
    exact localizedEtaleFieldPointPullback
  · exact geometricPointImageLift_of_strong strongEtaleFieldPointImageLift
      (fun K _ _ _ => (localizedEtaleStability (K := K)).2)

end Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

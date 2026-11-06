import Langlands.Geometry.Analytic.SpecialSetIntersectionOfIdealEffectiveness
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescentProof

/-! # Full local-domain intersections inside a special subset -/

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

/-- Two full local domains in a special subset have a full local-domain
intersection, and its actual completed-tensor restriction map is admissible. -/
theorem specialSetIntersection : SpecialSetIntersectionStatement.{u, v, w} :=
  specialSetIntersection_of_idealEffectiveness.{u, v, w}
    PresentedAffinoidAlgebra.Domain.FiniteCover.idealEffectiveness.{u}

end Langlands.Analytic.IndexedAffinoidAtlas

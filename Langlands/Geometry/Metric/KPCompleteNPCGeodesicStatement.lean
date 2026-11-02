import Langlands.Geometry.Metric.KPDefinitions

/-!
# Geodesic existence from completeness and primitive nonpositive curvature

This derived statement isolates the geodesic-existence obligation needed to use
KP Theorem 1.1.15 in Corollary 1.1.19. It states a consequence of completeness
and the midpoint inequality; it does not include geodesic existence in the NPC
predicate and does not prove the consequence.
-/

namespace Langlands.Geometry.Metric.KP

universe uX

/-- A complete metric space satisfying the primitive KP Definition 1.1.8 midpoint
condition is geodesic in the sense of KP Definition 1.1.4. This is a derived
construction target, with no nonemptiness, compactness or geodesic premise. -/
def CompleteNPCGeodesicStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X] [CompleteSpace X],
    IsNonpositivelyCurved X → IsGeodesicSpace X

end Langlands.Geometry.Metric.KP

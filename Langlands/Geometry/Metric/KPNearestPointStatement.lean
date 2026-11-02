import Langlands.Geometry.Metric.KPDefinitions

/-!
# Kaletha–Prasad nearest-point projection statement

The target of KP Proposition 1.1.20, read with the corrections of 1 November 2024.
This module states existence, uniqueness, continuity and equivariance of projection
onto a closed nonempty geodesically convex subset. It does not construct the projection
or prove any part of the target.
-/

open Set

namespace Langlands.Geometry.Metric.KP

universe uX

/-- KP Proposition 1.1.20: a closed convex subset of a complete NPC geodesic space
has a unique nearest point to each ambient point, and the resulting projection is
continuous and equivariant under every surjective isometry preserving the subset.
The subset can be unbounded, and the minimum distance can be zero. -/
def NearestPointProjectionStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X] [CompleteSpace X],
    IsNonpositivelyCurved X → IsGeodesicSpace X →
      ∀ Y : Set X, IsClosed Y → IsGeodesicallyConvex Y →
        ∃ π : X → Y,
          (∀ (x : X) (y : Y), dist x (π x : X) ≤ dist x (y : X)) ∧
            (∀ (x : X) (y : Y),
              dist x (y : X) = dist x (π x : X) → y = π x) ∧
              Continuous π ∧
                ∀ e : X ≃ᵢ X, e '' Y = Y →
                  ∀ x : X, (π (e x) : X) = e (π x : X)

end Langlands.Geometry.Metric.KP

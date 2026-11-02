import Langlands.Geometry.Metric.KPDefinitions
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Kaletha–Prasad metric fixed-point statements

Prop-valued targets for KP Lemmas 1.1.11 and 1.1.13, the hull assertion after
Definition 1.1.14, Theorem 1.1.15, and Corollary 1.1.19. The corrections of
1 November 2024 apply. These declarations state the results; they do not prove them.

In particular, geodesic existence is a hypothesis of the first four targets, whereas
Corollary 1.1.19 is stated for a complete nonpositively curved metric space without that
additional hypothesis. Boundedness and convexity use the published primitive definitions.
-/

open Set Bornology unitInterval
open scoped Langlands.Geometry.Metric.KP

namespace Langlands.Geometry.Metric.KP

universe uX uG

/-- KP Lemma 1.1.11: geodesics are unique, and their midpoint is exactly the point satisfying
the nonpositive-curvature inequality. Neither completeness nor local compactness is assumed. -/
def GeodesicUniquenessStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X],
    IsNonpositivelyCurved X → IsGeodesicSpace X →
      IsUniquelyGeodesicSpace X ∧
        ∀ (x y : X) (γ : Path x y), IsGeodesic γ →
          ∀ m : X, IsNPCMidpoint x y m ↔
            m = γ ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

/-- Corrected KP Lemma 1.1.13: a closed ball of nonnegative radius in an NPC geodesic space
is nonempty and contains every geodesic between its points. -/
def ClosedBallConvexityStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X],
    IsNonpositivelyCurved X → IsGeodesicSpace X →
      ∀ (z : X) (r : ℝ), 0 ≤ r →
        IsGeodesicallyConvex (Metric.closedBall z r)

/-- The assertion following corrected KP Definition 1.1.14: the specified intersection
really is a closed bounded convex superset of every nonempty bounded input. -/
def ClosedConvexHullStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X],
    IsNonpositivelyCurved X → IsGeodesicSpace X →
      ∀ M : Set X, M.Nonempty → IsBounded M →
        IsClosed (closedGeodesicConvexHull M) ∧
          IsBounded (closedGeodesicConvexHull M) ∧
            IsGeodesicallyConvex (closedGeodesicConvexHull M) ∧
              M ⊆ closedGeodesicConvexHull M

/-- KP Theorem 1.1.15(1): a nonempty bounded closed convex set has exactly one barycenter,
and each barycenter is fixed by every surjective isometry that maps the set onto itself.
Nonemptiness is part of the corrected convexity predicate. -/
def BarycenterStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X] [CompleteSpace X],
    IsNonpositivelyCurved X → IsGeodesicSpace X →
      ∀ M : Set X, IsBounded M → IsClosed M → IsGeodesicallyConvex M →
        (∃! b : X, IsBarycenter M b) ∧
          ∀ b : X, IsBarycenter M b →
            ∀ e : X ≃ᵢ X, e '' M = M → e b = b

/-- KP Theorem 1.1.15(2): one point is fixed simultaneously by all isometries preserving
an arbitrary nonempty bounded set. The preserved set need not be closed or convex. -/
def BoundedSetStabilizerFixedPointStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X] [CompleteSpace X],
    IsNonpositivelyCurved X → IsGeodesicSpace X →
      ∀ M : Set X, M.Nonempty → IsBounded M →
        ∃ b : X, ∀ e : X ≃ᵢ X, e '' M = M → e b = b

/-- KP Corollary 1.1.19 in the equivalent language of an arbitrary isometric group action.
There is no geodesic-existence hypothesis, no assumed fixed point and no topology on the group.
The two carrier universes are independent. -/
def BoundedActionFixedPointStatement : Prop :=
  ∀ (X : Type uX) [MetricSpace X] [CompleteSpace X] [Nonempty X],
    IsNonpositivelyCurved X →
      ∀ (G : Type uG) [Group G] [MulAction G X] [IsIsometricSMul G X],
        HasBoundedAction X (univ : Set G) → (MulAction.fixedPoints G X).Nonempty

/-- The complete source-statement interface for the metric fixed-point foundation.
This conjunction asserts every target above and assumes none of them as input. -/
def MetricFixedPointFoundationStatement : Prop :=
  GeodesicUniquenessStatement.{uX} ∧
    ClosedBallConvexityStatement.{uX} ∧
      ClosedConvexHullStatement.{uX} ∧
        BarycenterStatement.{uX} ∧
          BoundedSetStabilizerFixedPointStatement.{uX} ∧
            BoundedActionFixedPointStatement.{uX, uG}

end Langlands.Geometry.Metric.KP

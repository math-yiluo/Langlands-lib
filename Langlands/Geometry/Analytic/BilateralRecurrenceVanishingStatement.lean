import Langlands.Geometry.Analytic.ClosedIdealsBanach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! # Vanishing of decaying bilateral multiplication recurrences -/

open Topology

universe u v

namespace Langlands.Analytic

/-- A bilateral sequence tending to zero outside finite subsets and satisfying
the multiplication recurrence vanishes in a Noetherian Banach algebra. -/
def BilateralRecurrenceVanishingStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K]
    (A : Type v) [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsNoetherianRing A]
    (f : A) (c : ℤ → A),
    Filter.Tendsto c Filter.cofinite (nhds 0) →
    (∀ n : ℤ, c (n - 1) = f * c n) →
    ∀ n : ℤ, c n = 0

end Langlands.Analytic

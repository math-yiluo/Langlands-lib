import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialChart
import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution

/-! # Straightening products in small exponential coordinates -/

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Metric

/-- On sufficiently small norm balls, products of exponentials become sums
after an isometric bijection that conjugates each coordinate by a controlled unit. -/
def ExponentialProductStraighteningStatement (F A : Type*) [NontriviallyNormedField F]
    [CharZero F] [IsUltrametricDist F] [NormedRing A] [NormedAlgebra F A]
    [IsUltrametricDist A] [CompleteSpace A] : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∃ ε : ℝ, 0 < ε ∧ c * ε < 1 ∧
    ∀ r : ℝ, 0 < r → r ≤ ε →
      let L := closedBall (0 : A) r
      ∃ Φ : (L × L) ≃ᵢ (L × L),
        ∀ x : L × L,
          NormedSpace.exp (((Φ x).1 : A) + ((Φ x).2 : A)) =
            NormedSpace.exp (x.1 : A) * NormedSpace.exp (x.2 : A) ∧
          ∃ u v : Aˣ, ‖(u : A) - 1‖ ≤ c * r ∧ ‖(v : A) - 1‖ ≤ c * r ∧
            ((Φ x).1 : A) = conjugationHomeomorph u (x.1 : A) ∧
            ((Φ x).2 : A) = conjugationHomeomorph v (x.2 : A)

end Langlands.HarmonicAnalysis.UnitConjugation

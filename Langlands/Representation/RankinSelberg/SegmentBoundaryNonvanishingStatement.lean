import Langlands.Representation.RankinSelberg.SegmentGammaTelescopingStatement

noncomputable section

namespace Langlands.RankinSelberg

open SegmentGammaTelescoping

/-- The first-row polynomial of an ordered pair of centered segments has no
zero in the open unit disk when its base parameters have norm at most one. -/
def SegmentBoundaryNonvanishingStatement : Prop :=
  ∀ (A : Finset ℂˣ) (t : ℂˣ) (m n : ℕ),
    n ≤ m → ‖(t : ℂ)‖ ≤ 1 → (∀ a ∈ A, ‖(a : ℂ)‖ ≤ 1) →
    ∀ z : ℂ, ‖z‖ < 1 →
      (∏ a ∈ A, boundaryPolynomial a t m n).eval z ≠ 0

end Langlands.RankinSelberg

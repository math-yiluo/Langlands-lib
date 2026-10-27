import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover

/-! # Scalar descent for the binary unit-radius Laurent cover -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Scalar sections of the two actual binary Laurent quotients whose
restrictions to the actual overlap quotient agree descend uniquely to the
presented strict affinoid base algebra. -/
def BinaryLaurentGluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (f : P)
    (sUpper : (laurentUpper f).algebra) (sLower : (laurentLower f).algebra),
    (interLeft (laurentUpper f) (laurentLower f)).restriction sUpper =
      (interRight (laurentUpper f) (laurentLower f)).restriction sLower →
    ∃! a : P, (laurentUpper f).baseMap a = sUpper ∧
      (laurentLower f).baseMap a = sLower

end Langlands.Analytic.StrictTestDomain

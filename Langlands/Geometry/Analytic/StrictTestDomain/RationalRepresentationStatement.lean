import Langlands.Geometry.Analytic.StrictTestDomain.Definitions

/-! # Rational representation with presented strict affinoid tests -/

universe u

namespace Langlands.Analytic.StrictTestDomain

/-- The actual rational quotient represents its closed rational locus for all
presented strict affinoid tests. The rational inputs have no common spectrum
zero; no unit-ideal certificate or factorization is supplied separately. -/
def RationalRepresentationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (d : RationalData K P),
    Represents K d.baseMap d.locus

end Langlands.Analytic.StrictTestDomain

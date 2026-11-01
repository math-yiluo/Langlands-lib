import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescent
import Langlands.Geometry.Analytic.StrictTestDomain.IteratedLaurentCover

/-! # Universal scalar descent for finite iterated Laurent covers -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Every finite iterated unit-radius Laurent family has scalar descent after
every bounded base change to a presented strict affinoid algebra. -/
def IteratedLaurentScalarDescentStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) (g : Fin m → P),
    UniversalScalarCoverDescent (fun ε : Fin m → Bool => iteratedLaurent g ε)

end Langlands.Analytic.StrictTestDomain

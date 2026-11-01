import Langlands.Geometry.Analytic.StrictTestDomain.ScalarCoverDescent
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalCover

/-! # Scalar descent for standard covers of tuples of units -/

universe u

namespace Langlands.Analytic.StrictTestDomain

open RationalData

/-- Every standard rational cover of a finite tuple of units without common
spectrum zero has scalar descent, over every complete ultrametric normed field. -/
def AllUnitStandardRationalGluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (n : ℕ) (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0),
    (∀ j, IsUnit (f j)) → ScalarCoverDescent (standardRational f hf)

end Langlands.Analytic.StrictTestDomain

import Langlands.Geometry.Analytic.StrictTestDomain.RationalTensorComparison
import Mathlib.RingTheory.RingHom.Finite

/-! # Finite rational tensor comparison target -/

universe u

namespace Langlands.Analytic.StrictTestDomain

/-- For a finite bounded map of actual presented strict affinoid algebras,
the canonical ordinary tensor comparison to the pulled-back rational quotient
is bijective. This is a proposition to be proved separately. -/
def FiniteRationalTensorComparisonStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P Q : PresentedStrictAffinoidAlgebra K) (d : RationalData K P)
    (φ : BoundedAlgHom K P Q),
    φ.toAlgHom.toRingHom.Finite → Function.Bijective (d.tensorComparison φ)

end Langlands.Analytic.StrictTestDomain

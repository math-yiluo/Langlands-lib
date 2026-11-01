import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain

/-! # Finite rational coverage of every full affinoid domain -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory

/-- Every full represented affinoid domain has a finite covering by actual
positive-radius rational charts of its ambient base. Each piece has an
actual bounded restriction from the represented domain algebra. -/
def FiniteRationalCoverStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (U : Domain K A),
    ∃ (n : ℕ) (D : Fin n → RationalChart K A)
      (_ : ∀ i, (D i).toDomain ⟶ U),
      ∀ x ∈ U.locus, ∃ i, x ∈ (D i).locus

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain

import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.MatchingAlgebra

/-! # Global generation of finite Banach descent data by matching elements -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Finitely many elements of the constructed complete matching algebra generate
every original local finite algebra as a module over its original cover algebra. -/
def FiniteAffinoidAlgebraGlobalGenerationStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (R : PresentedAffinoidAlgebra K)
    (c : Domain.FiniteCover (Domain.whole K R))
    (F : FiniteAffinoidAlgebraDescent.LocalAlgebras c)
    (d : FiniteAffinoidAlgebraDescent.DescentData F),
    ∃ (n : ℕ) (s : Fin n → d.toPairTransitions.MatchingAlgebra),
      ∀ i, Function.Surjective
        ((F.map i).coefficientMap fun k => d.toPairTransitions.projection i (s k))

end Langlands.Analytic.PresentedAffinoidAlgebra

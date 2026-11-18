import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.EffectiveData

/-! # Effective finite Banach algebra descent from global generation -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- For every actual finite Banach descent datum, finitely many matching elements
that generate every original local algebra as a module over its original cover
algebra yield the complete effective realization of that datum. -/
def FiniteAffinoidAlgebraGlobalGenerationReductionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (R : PresentedAffinoidAlgebra K)
    (c : Domain.FiniteCover (Domain.whole K R))
    (F : FiniteAffinoidAlgebraDescent.LocalAlgebras c)
    (d : FiniteAffinoidAlgebraDescent.DescentData F)
    (n : ℕ) (s : Fin n → d.toPairTransitions.MatchingAlgebra),
    (∀ i, Function.Surjective
      ((F.map i).coefficientMap fun k => d.toPairTransitions.projection i (s k))) →
    Nonempty (FiniteAffinoidAlgebraDescent.EffectiveRealization d)

end Langlands.Analytic.PresentedAffinoidAlgebra

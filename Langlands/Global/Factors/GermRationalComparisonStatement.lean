import Langlands.Global.Factors.FiniteComparisonStatement
import Langlands.Representation.RankinSelberg.RationalContinuation

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.FunctionalEquationComparison

/-- Germ equality identifies supplied rational continuations. Their denominator
regularity on right half-planes is part of the continuation hypotheses. -/
def GermRationalComparisonStatement : Prop :=
  ∀ (q : ℕ), 1 < q →
  ∀ (f g : ℂ → ℂ) (R S : RatFunc ℂ),
    RankinSelberg.HasRationalContinuation q f R →
    RankinSelberg.HasRationalContinuation q g S →
    MeromorphicEq f g → R = S

end Langlands.Global.FunctionalEquationComparison

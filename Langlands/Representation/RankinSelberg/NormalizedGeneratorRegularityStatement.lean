import Langlands.Representation.RankinSelberg.RationalZeta
import Langlands.Representation.RankinSelberg.RationalEvaluation

/-!
# Regularity of normalized reciprocal generators

This internal algebraic interface separates the Laurent-module argument from
the analytic regularity of individual Rankin–Selberg integrals.
-/

namespace Langlands.RankinSelberg

/-- If every rational value generating a Laurent module is regular at a
nonzero complex point, its normalized generator polynomial has no zero there.
This is a statement, not a proof of the algebraic implication. -/
def NormalizedGeneratorRegularityStatement : Prop :=
  ∀ (values : Set RationalFunctions) (P : Polynomial ℂ),
    IsNormalizedGenerator values P →
    ∀ z : ℂ, z ≠ 0 →
      (∀ R ∈ values, RationalEvaluation.RegularAt R z) →
      P.eval z ≠ 0

end Langlands.RankinSelberg

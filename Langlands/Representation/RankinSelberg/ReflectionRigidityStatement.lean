import Langlands.LocalFactor.WeilDelignePair

namespace Langlands.RankinSelberg

/-- Normalized complex polynomials related by reciprocal reflection and a Laurent
monomial are both one when their root-exclusion radii have a strict product gap.
This declaration states the internal algebraic result; it does not prove it. -/
def ReflectionRigidityStatement : Prop :=
  ∀ (a b : ℝ) (δ c : ℂˣ) (m : ℤ) (D E : Polynomial ℂ),
    0 < a →
    0 < b →
    ‖(δ : ℂ)‖ < a * b →
    D.coeff 0 = 1 →
    E.coeff 0 = 1 →
    (∀ z : ℂ, ‖z‖ < a → D.eval z ≠ 0) →
    (∀ z : ℂ, ‖z‖ < b → E.eval z ≠ 0) →
    algebraMap (Polynomial ℂ) (RatFunc ℂ) D =
      (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
        LocalFactor.RationalReflection.subst δ
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) E) →
    D = 1 ∧ E = 1

end Langlands.RankinSelberg

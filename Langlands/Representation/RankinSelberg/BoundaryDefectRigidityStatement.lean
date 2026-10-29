import Langlands.LocalFactor.WeilDelignePair

namespace Langlands.RankinSelberg

/-- Two normalized polynomial defects are both one when each cancels against a
known tail divisor, the cofactors exclude roots from separated disks, and the
defects are related by reciprocal reflection and a Laurent monomial. The
equations then identify the two boundary polynomials as products. This
declaration states the internal algebraic result; it does not prove it. -/
def BoundaryDefectRigidityStatement : Prop :=
  ∀ (a b : ℝ) (δ c : ℂˣ) (m : ℤ)
    (A C P D Adual Cdual Pdual E : Polynomial ℂ),
    0 < a →
    0 < b →
    ‖(δ : ℂ)‖ < a * b →
    A.coeff 0 = 1 →
    C.coeff 0 = 1 →
    P.coeff 0 = 1 →
    Adual.coeff 0 = 1 →
    Cdual.coeff 0 = 1 →
    Pdual.coeff 0 = 1 →
    A * C = D * P →
    Adual * Cdual = E * Pdual →
    A ∣ P →
    Adual ∣ Pdual →
    (∀ z : ℂ, ‖z‖ < a → C.eval z ≠ 0) →
    (∀ z : ℂ, ‖z‖ < b → Cdual.eval z ≠ 0) →
    algebraMap (Polynomial ℂ) (RatFunc ℂ) D =
      (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
        LocalFactor.RationalReflection.subst δ
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) E) →
    D = 1 ∧ E = 1 ∧ P = A * C ∧ Pdual = Adual * Cdual

end Langlands.RankinSelberg

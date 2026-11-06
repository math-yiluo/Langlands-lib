import Langlands.LocalFactor.WeilDelignePair

namespace Langlands.RankinSelberg

/-- Root separation makes the normalized polynomial in a rational gamma
decomposition unique, even without polynomial divisibility. -/
def GammaDecompositionUniquenessStatement : Prop :=
  ∀ (a b : ℝ) (δ c : ℂˣ) (m : ℤ) (P PD B BD : Polynomial ℂ),
    0 < a →
    0 < b →
    ‖(δ : ℂ)‖ < a * b →
    P.coeff 0 = 1 →
    B.coeff 0 = 1 →
    (∀ z : ℂ, ‖z‖ < a → P.eval z ≠ 0) →
    (∀ z : ℂ, ‖z‖ < a → B.eval z ≠ 0) →
    (∀ z : ℂ, ‖z‖ < b → PD.eval z ≠ 0) →
    (∀ z : ℂ, ‖z‖ < b → BD.eval z ≠ 0) →
    algebraMap (Polynomial ℂ) (RatFunc ℂ) B *
        LocalFactor.RationalReflection.subst δ
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) PD) =
      (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
        algebraMap (Polynomial ℂ) (RatFunc ℂ) P *
          LocalFactor.RationalReflection.subst δ
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) BD) →
    P = B

end Langlands.RankinSelberg

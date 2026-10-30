import Langlands.Global.ArchimedeanCartanPolynomialCoefficients

/-! # Analyticity of the actual Cartan polynomial coefficient arrays -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Every coefficient of the explicitly constructed coordinate operator is real analytic
on the entire original ambient matrix space, for every complex polynomial. -/
def CartanPolynomialCoefficientAnalyticityStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ p : Polynomial ℂ,
    (cartanPolynomialCoordinateOperator K n p).AnalyticCoefficientsOn Set.univ

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CartanPolynomialCoefficientAnalyticityStatement

end Langlands.Global.ArchimedeanGL

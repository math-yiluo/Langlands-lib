import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Langlands.Global.ArchimedeanCartanAmbientOperator
import Langlands.Global.ArchimedeanCartanSymbolBounds

/-! # Coordinate realization and leading symbol of monic Cartan polynomials -/

noncomputable section
universe u
open scoped Classical ContDiff Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- An actual finite coordinate operator realizes each monic ambient Cartan polynomial
on smooth functions, with analytic coefficients and the expected highest-order symbol. -/
def CartanPolynomialCoordinateRealizationStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ p : Polynomial ℂ, p.Monic →
    ∃ (d : ℕ)
      (D : Langlands.Analysis.CoordinateScalarOperator
        (ArchimedeanMatrix K n) d (2 * p.natDegree)),
      D.AnalyticCoefficientsOn
        (Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) ∧
      (∀ F : ArchimedeanMatrix K n → ℂ,
        ContDiffOn ℝ ∞ F
          (Set.range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) →
        ∀ g : ArchimedeanGL K n,
          D.action F (g : ArchimedeanMatrix K n) =
            cartanAmbientPolynomial K n p F (g : ArchimedeanMatrix K n)) ∧
      (∀ (g : ArchimedeanGL K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ),
        D.principalSymbol (g : ArchimedeanMatrix K n) ξ =
          (ambientCartanCovectorForm K n (g : ArchimedeanMatrix K n) ξ : ℂ) ^
            p.natDegree)

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CartanPolynomialCoordinateRealizationStatement

end Langlands.Global.ArchimedeanGL

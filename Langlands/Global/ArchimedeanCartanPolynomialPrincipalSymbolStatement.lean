import Langlands.Global.ArchimedeanCartanPolynomialCoefficients
import Langlands.Global.ArchimedeanCartanSymbolBounds

/-! # Principal symbol of the actual monic Cartan polynomial operator -/

noncomputable section
universe u
open scoped Classical Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- The actual monic polynomial coefficient array has the predicted leading symbol
at every ambient matrix and every real continuous covector. -/
def CartanPolynomialPrincipalSymbolStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∀ p : Polynomial ℂ, p.Monic →
    ∀ (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ),
      (cartanPolynomialCoordinateOperator K n p).principalSymbol y ξ =
        (ambientCartanCovectorForm K n y ξ : ℂ) ^ p.natDegree

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @CartanPolynomialPrincipalSymbolStatement

/-- The left side is the published symbol: top-order coefficients of the actual array,
paired with real covector evaluations on the fixed coordinate basis. -/
example (K : Type u) [Field K] [NumberField K] (n : ℕ) (p : Polynomial ℂ)
    (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    (cartanPolynomialCoordinateOperator K n p).principalSymbol y ξ =
      ∑ w : Fin (2 * p.natDegree) → Fin (cartanCoordinateDimension K n),
        (cartanPolynomialCoordinateOperator K n p).coefficient
            (Fin.last (2 * p.natDegree)) w y *
          ∏ j : Fin (2 * p.natDegree), (ξ (cartanCoordinateBasis K n (w j)) : ℂ) :=
  rfl

/-- The right side is the actual Cartan sum of squares over the full real Cartan basis. -/
example (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (y : ArchimedeanMatrix K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    ambientCartanCovectorForm K n y ξ =
      ∑ i : CartanBasisIndex K n, (ξ (cartanMatrixField K n i y)) ^ 2 :=
  rfl

/-- Restricted to actual units, the statement gives the symbol clause of the published
coordinate realization statement for this particular operator. -/
example (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (h : CartanPolynomialPrincipalSymbolStatement K n) (p : Polynomial ℂ) (hp : p.Monic)
    (g : ArchimedeanGL K n) (ξ : ArchimedeanMatrix K n →L[ℝ] ℝ) :
    (cartanPolynomialCoordinateOperator K n p).principalSymbol
        (g : ArchimedeanMatrix K n) ξ =
      (ambientCartanCovectorForm K n (g : ArchimedeanMatrix K n) ξ : ℂ) ^ p.natDegree :=
  h p hp g ξ

end Langlands.Global.ArchimedeanGL

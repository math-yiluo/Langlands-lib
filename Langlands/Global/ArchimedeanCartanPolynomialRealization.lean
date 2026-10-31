import Langlands.Global.ArchimedeanCartanPolynomialRealizationStatement
import Langlands.Global.ArchimedeanCartanPolynomialAction
import Langlands.Global.ArchimedeanCartanPolynomialPrincipalSymbol

/-! # Coordinate realization of the actual monic Cartan polynomial -/

noncomputable section
universe u
open scoped Classical ContDiff Matrix.Norms.Operator
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual recursive coordinate operator supplies the published realization. -/
theorem cartanPolynomialCoordinateRealization :
    CartanPolynomialCoordinateRealizationStatement K n := by
  intro p hp
  refine ⟨cartanCoordinateDimension K n, cartanPolynomialCoordinateOperator K n p,
    (cartanPolynomialCoordinateOperator_analyticCoefficients K n p).mono (Set.subset_univ _),
    ?_, ?_⟩
  · intro F hF g
    exact cartanPolynomialCoordinateOperator_action K n p F
      Units.isOpenEmbedding_val.isOpen_range hF (g : ArchimedeanMatrix K n) ⟨g, rfl⟩
  · intro g ξ
    exact cartanPolynomialCoordinateOperator_principalSymbol K n p hp
      (g : ArchimedeanMatrix K n) ξ

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    CartanPolynomialCoordinateRealizationStatement K n :=
  @cartanPolynomialCoordinateRealization

end Langlands.Global.ArchimedeanGL

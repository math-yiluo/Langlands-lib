import Langlands.Representation.Classification.ProductLeviSquareIntegrableLpStatement
import Langlands.Representation.Classification.TemperedDiscreteSeriesIsotypicStatement

/-! # Reduction of discrete-series isotypic projectors to exponents below two -/

namespace Langlands

universe uF uV uW

/-- Integrability of discrete-series coefficients below exponent two implies the
unchanged tempered discrete-series isotypic projector statement. -/
def GLTemperedDiscreteSeriesIsotypicReductionStatement : Prop :=
  GLProductLeviSquareIntegrableLpStatement.{uF, uW} →
    GLTemperedDiscreteSeriesIsotypicStatement.{uF, uV, uW}

end Langlands

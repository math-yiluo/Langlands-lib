import Langlands.Representation.Classification.TemperedDiscreteSeriesIsotypicReductionProof
import Langlands.Representation.Classification.ProductLeviSquareIntegrableLpProof

/-! # Discrete-series isotypic projectors in tempered Levi representations (proof) -/

namespace Langlands

universe uF uV uW

/-- For a tempered representation `ρ` of a standard GL block Levi and an irreducible
square-integrable `σ` with the same central character, the `σ`-isotypic
subrepresentation of `ρ` is the range of an idempotent self-intertwiner whose
kernel has no subrepresentation mapping onto `σ`. -/
theorem glTemperedDiscreteSeriesIsotypic :
    GLTemperedDiscreteSeriesIsotypicStatement.{uF, uV, uW} :=
  glTemperedDiscreteSeriesIsotypicReduction glProductLeviSquareIntegrableLp

end Langlands

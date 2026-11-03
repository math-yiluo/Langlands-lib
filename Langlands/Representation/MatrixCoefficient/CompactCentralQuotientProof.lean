import Langlands.Representation.MatrixCoefficient.CompactCentralQuotientStatement
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Square integrability on a compact full central quotient -/

namespace Langlands

theorem compactCentralQuotientSquareIntegrability.{uG, uV} :
    CompactCentralQuotientSquareIntegrabilityStatement.{uG, uV} := by
  intro G V _ _ _ _ _ _ _ _ ρ hρ ⟨c⟩ μ _
  refine ⟨hρ, c, ?_⟩
  intro ℓ v
  exact (c.continuous_coefficientNorm ℓ v (hρ.1 v)).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end Langlands

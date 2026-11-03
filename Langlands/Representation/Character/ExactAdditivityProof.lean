import Langlands.Representation.Character.ExactK0Targets
import Langlands.LinearAlgebra.FiniteRankTraceExact

/-! # Additivity of the actual distribution character on short exact sequences -/

noncomputable section

universe uG uA uB uC

namespace Langlands.Character

/-- The actual distribution character is additive on every admissible short
exact sequence, including those that do not split equivariantly. -/
theorem distributionShortExactAdditivity :
    DistributionShortExactAdditivityStatement.{uG, uA, uB, uC} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ A B C hA hB hC f g h
  ext φ
  change FiniteRankEnd.trace (finiteRankIntegratedAction μ B.representation hB φ) =
    FiniteRankEnd.trace (finiteRankIntegratedAction μ A.representation hA φ) +
      FiniteRankEnd.trace (finiteRankIntegratedAction μ C.representation hC φ)
  apply FiniteRankEnd.trace_shortExact f.toLinearMap g.toLinearMap h.1 h.2.1 h.2.2
  · ext a
    exact (Hecke.integratedAction_intertwiner μ hA.1 hB.1 f φ a).symm
  · ext b
    exact Hecke.integratedAction_intertwiner μ hB.1 hC.1 g φ b

end Langlands.Character

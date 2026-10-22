import Langlands.Representation.Hecke.LocalUnitsStatement
import Langlands.Representation.Hecke.CommonInvarianceProof

universe u

namespace Langlands.Hecke.HeckeAlgebra

/-- The normalized compact-open indicators supply two-sided local units. -/
theorem finiteFamilyLocalUnits : FiniteFamilyLocalUnitsStatement.{u} := by
  intro G _ _ _ _ _ _ _ _ μ _ s U
  obtain ⟨K, hKU, hK, hKs⟩ := TestFunction.commonCompactOpenBiInvariance G s U
  refine ⟨K, hK, hKU, normalizedIndicator_idempotent μ K hK, ?_⟩
  intro f hf
  exact ⟨normalizedIndicator_mul_of_leftInvariant μ K hK f (hKs f hf).1,
    mul_normalizedIndicator_of_rightInvariant μ K hK f (hKs f hf).2⟩

end Langlands.Hecke.HeckeAlgebra

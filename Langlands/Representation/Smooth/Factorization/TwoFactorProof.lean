import Langlands.Representation.Smooth.Factorization.TwoFactorFixedVectorsProof
import Langlands.Representation.Smooth.Factorization.TwoFactorExternalTensorProof
import Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
import Langlands.Representation.Smooth.Factorization.TwoFactorUniquenessProof

/-! # Two-factor decomposition of admissible representations -/

namespace Langlands

universe uG₁ uG₂ uV₁ uV₂ uW₁ uW₂ uV

/-- The four clauses of Flath's two-factor theorem, with all independent
universes and the hypotheses of the published statement preserved. -/
theorem flathTwoFactor :
    FlathTwoFactorStatement.{uG₁, uG₂, uV₁, uV₂, uW₁, uW₂, uV} :=
  ⟨productFixedVectors, admissibleExternalTensor,
    admissibleProductFactorization, admissibleProductFactorUniqueness⟩

end Langlands

import Langlands.Representation.Smooth.RenardCoinvariantTensorStatements
import Langlands.Representation.Smooth.RenardTensorHomExactnessProof

namespace Langlands.Renard.Smooth

universe u v

/-- Renard III.1.14–III.1.15: the diagonal tensor of smooth representations is smooth. -/
theorem tensorProductSmooth : TensorProductSmoothStatement.{u, v} := by
  intro G _ _ _ _ _ V W _ _ _ _ ρ σ hρ hσ
  exact TensorHom.tensor_smooth ρ σ hρ hσ

end Langlands.Renard.Smooth

import Langlands.Algebra.AlgebraTensorSimpleModuleStatements
import Langlands.Algebra.AlgebraTensorSimpleFactorizationProof
import Langlands.Algebra.AlgebraTensorFactorUniquenessProof

namespace Langlands

universe u₁ u₂ v v₁ v₂ w₁ w₂

/-- The three assertions of Renard III.1.14, Scholium, with independent universes. -/
theorem algebraTensorScholium :
    AlgebraTensorScholiumStatement.{u₁, u₂, v, v₁, v₂, w₁, w₂} :=
  ⟨algebraExternalTensorSimple, algebraTensorSimpleFactorization, algebraTensorFactorUniqueness⟩

end Langlands

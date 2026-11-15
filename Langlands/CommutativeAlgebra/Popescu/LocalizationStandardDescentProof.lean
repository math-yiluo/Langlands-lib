import Langlands.CommutativeAlgebra.Popescu.LocalizationStandardDescentAssembly
import Langlands.CommutativeAlgebra.Popescu.StandardSmoothRetractProof

/-! # Proof of Stacks Lemma 8.3 (07F4), strictly standard form -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.8.3 (07F4), strictly standard form. -/
theorem localizationStandardDescent : LocalizationStandardDescentStatement.{u} :=
  localizationStandardDescent_of StandardSmoothRetract.standardSmoothRetract

end Langlands.CommutativeAlgebra.Popescu

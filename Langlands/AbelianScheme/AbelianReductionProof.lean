import Langlands.AbelianScheme.AbelianReductionOfProperClosedFibre
import Langlands.AlgebraicGeometry.SmoothDvrProperClosedFibreProof

/-! # Abelian reduction of a Néron model -/

universe u

namespace Langlands.AbelianScheme

/-- A Néron model with proper geometric special identity component is abelian. -/
theorem abelianReduction : AbelianReductionStatement.{u} :=
  abelianReduction_of_properClosedFibre AlgebraicGeometry.smoothDvrProperClosedFibre

end Langlands.AbelianScheme

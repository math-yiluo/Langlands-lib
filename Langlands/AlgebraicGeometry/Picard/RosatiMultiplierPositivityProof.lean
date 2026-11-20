import Langlands.AlgebraicGeometry.Picard.RosatiMultiplierPositivityStatement
import Langlands.AlgebraicGeometry.Picard.RosatiMultiplierPositivityReduction
import Langlands.AlgebraicGeometry.Picard.RosatiPositivityProof

/-! # Positivity of actual rational self-isogeny multipliers -/

universe u

namespace Langlands.AbelianScheme.Rosati

/-- An actual rational self-isogeny satisfying the dual-pullback equation has
positive multiplier when the abelian scheme has nonzero rational identity. -/
theorem multiplierPositivity : MultiplierPositivityStatement.{u} :=
  multiplierPositivity_of_positivity positivity.{u}

end Langlands.AbelianScheme.Rosati

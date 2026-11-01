import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerFiniteTypeNormalizationProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IntegerFiniteTypeNormalizationReductionProof

/-! # Normal finitely generated subalgebras of an integrally closed domain -/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Every finite subset of an integrally closed domain lies in a normal,
noetherian, finitely generated integer subalgebra. -/
theorem normalFiniteTypeSubalgebra : NormalFiniteTypeSubalgebraStatement.{u} :=
  integerFiniteTypeNormalizationReduction.{u} integerFiniteTypeNormalization.{u}

end Langlands.AlgebraicGeometry.NoetherianApproximation

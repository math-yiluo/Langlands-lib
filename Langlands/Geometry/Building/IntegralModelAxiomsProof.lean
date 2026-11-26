import Langlands.BruhatTits.IntegralModels.IntegralModelAxiomsConditional
import Langlands.Geometry.Building.UnramifiedApartmentDescentProof
import Langlands.Geometry.Building.UnramifiedZeroDescentProof

/-! # Integral models with Axioms 4.1.20 and 4.1.22 on supplied building data -/

universe u

namespace Langlands.Geometry.Building

/-- Construct the integral model and reductive quotient families on supplied
building data satisfying the corrected Section 4.2 axioms, by unramified descent. -/
theorem integralModelAxioms : IntegralModelAxiomsStatement.{u} :=
  BruhatTits.IntegralModels.integralModelAxiomsStatement_of_unramified_remaining
    unramifiedApartmentDescent unramifiedZeroDescent

end Langlands.Geometry.Building

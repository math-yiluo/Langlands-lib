import Langlands.Representation.Compact.UnitaryAdmissibleEndomorphismProof
import Langlands.Representation.Compact.EssentiallySquareIntegrableAdmissibleProof
import Langlands.Representation.Compact.SquareIntegrableUnitarySemisimpleProof
import Langlands.Representation.Compact.SchurOrthogonalityProof
import Langlands.Representation.Compact.CoefficientLinearIndependenceProof

namespace Langlands.Renard.CompactRepresentation

universe u v

/-- Renard IV.2.2 and IV.3.2–IV.3.3: the five unitary and square-integrable
representation statements, assembled from their component proofs. -/
theorem unitarySquareIntegrable : UnitarySquareIntegrableStatements.{u, v} :=
  ⟨unitaryAdmissibleEndomorphism, essentiallySquareIntegrableAdmissible,
    squareIntegrableUnitarySemisimple, schurOrthogonality, coefficientLinearIndependence⟩

end Langlands.Renard.CompactRepresentation

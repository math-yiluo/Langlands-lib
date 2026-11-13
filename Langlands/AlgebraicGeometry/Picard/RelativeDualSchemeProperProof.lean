import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeProperReduction
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFinitePresentationProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeQuasiCompactProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceProof

/-! # Properness of the chosen dual parameter scheme over a quasi-separated base -/

universe u

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the structural morphism of the actual chosen dual
parameter scheme is proper. -/
theorem relativeDualSchemeProper : RelativeDualSchemeProperStatement.{u} :=
  relativeDualSchemeProper_of_prerequisites
    ⟨relativeDualSchemeFinitePresentation.{u}, relativeDualSchemeQuasiCompact.{u},
      relativeDualSchemeValuativeExistence.{u}⟩

end Langlands.AbelianScheme

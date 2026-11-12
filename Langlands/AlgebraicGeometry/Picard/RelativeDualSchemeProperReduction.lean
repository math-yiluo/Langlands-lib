import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeProperStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeSeparatedProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeFinitePresentationStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeQuasiCompactStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceStatement

/-! # Conditional assembly of properness for the chosen dual parameter scheme -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The three independently supplied inputs to the properness assembly.
Separatedness is already available as a published theorem. -/
structure RelativeDualSchemeProperInputs : Prop where
  finitePresentation : RelativeDualSchemeFinitePresentationStatement.{u}
  quasiCompact : RelativeDualSchemeQuasiCompactStatement.{u}
  valuativeExistence : RelativeDualSchemeValuativeExistenceStatement.{u}

/-- The supplied inputs and the published separatedness proof imply properness
of the actual chosen dual. -/
theorem relativeDualSchemeProper_of_prerequisites
    (inputs : RelativeDualSchemeProperInputs.{u}) :
    RelativeDualSchemeProperStatement.{u} := by
  intro S _ A hA
  let := relativeDualSchemeSeparated S A hA
  let := inputs.finitePresentation S A hA
  let := inputs.quasiCompact S A hA
  let := UniversallyClosed.of_valuativeCriterion (dualScheme A hA).hom
    (inputs.valuativeExistence S A hA)
  exact {}

end Langlands.AbelianScheme

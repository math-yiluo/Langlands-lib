import Langlands.GroupScheme.Absolute.UnipotentAllBorelsEnvelope
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.Absolute.SolvableUnipotentPart
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # A normal unipotent envelope for a subgroup contained in every Borel -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected unipotent closed subgroup contained in every Borel lies
in a smooth connected normal unipotent closed subgroup. -/
theorem unipotentAllBorelsEnvelope : UnipotentAllBorelsEnvelopeStatement.{u} :=
  UnipotentAllBorelsEnvelope.unipotentAllBorelsEnvelope_of_statements
    ImageGeneration.pointedImageGeneration solvableUnipotentPart unipotentClosedSubgroup

end Langlands.GroupScheme

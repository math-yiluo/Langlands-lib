import Mathlib.CategoryTheory.Adjunction.Limits
import Langlands.CategoryTheory.Renard.AdjunctionPreservationStatements

/-!
# Renard A.V.2: proof that adjoints preserve limits and colimits

Proofs of the closed statements for the A.V.2 preservation theorem. Each
supplied limiting cone, or colimiting cocone, is mapped to a limiting cone, or
colimiting cocone, by Mathlib's arbitrary-universe adjunction argument.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.AdjunctionPreservation

universe vA uA vB uB vI uI

/-- The right adjoint `F` maps the supplied limiting cone to a limiting cone. -/
theorem rightAdjointPreservesLimitsStatement_proof :
    RightAdjointPreservesLimitsStatement.{vA, uA, vB, uB, vI, uI} := by
  intro A _ B _ G F adj I _ D t ⟨ht⟩
  have hF : PreservesLimitsOfSize.{vI, uI} F := adj.rightAdjoint_preservesLimits
  exact hF.preservesLimitsOfShape.preservesLimit.preserves ht

/-- The left adjoint `G` maps the supplied colimiting cocone to a colimiting cocone. -/
theorem leftAdjointPreservesColimitsStatement_proof :
    LeftAdjointPreservesColimitsStatement.{vA, uA, vB, uB, vI, uI} := by
  intro A _ B _ G F adj I _ D t ⟨ht⟩
  have hG : PreservesColimitsOfSize.{vI, uI} G := adj.leftAdjoint_preservesColimits
  exact hG.preservesColimitsOfShape.preservesColimit.preserves ht

/-- Renard A.V.2: right adjoints preserve limits and left adjoints preserve colimits. -/
theorem adjunctionPreservationStatements_proof :
    AdjunctionPreservationStatements.{vA, uA, vB, uB, vI, uI} :=
  ⟨rightAdjointPreservesLimitsStatement_proof, leftAdjointPreservesColimitsStatement_proof⟩

end Langlands.Renard.AdjunctionPreservation

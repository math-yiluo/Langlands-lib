import Langlands.Representation.Compact.CompactGroupSmoothRepresentationProof
import Langlands.Representation.Compact.AdmissibleFiniteMultiplicityProof

/-! # Renard IV.1.1–IV.1.2: smooth compact-group representations and finite multiplicities -/

namespace Langlands.Renard.CompactRepresentation

universe u v

/-- The two exact statements of Renard IV.1.1 and IV.1.2. -/
theorem compactGroupSmoothStatements : CompactGroupSmoothStatements.{u, v} :=
  ⟨compactGroupSmoothRepresentation, admissibleFiniteMultiplicity⟩

end Langlands.Renard.CompactRepresentation

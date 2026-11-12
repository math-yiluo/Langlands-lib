import Langlands.Representation.CompactCoefficient.SmoothEndomorphismTensorProof
import Langlands.Representation.CompactCoefficient.FormalDegreeOrthogonality
import Langlands.Representation.CompactCoefficient.CompactGroupFormalDegreeProof

/-! # Renard IV.1.4: coefficients, smooth endomorphisms and formal degree -/

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.4.1, the coefficient Proposition and the compact-group formal
degree formula, with the exact published universe parameters and hypotheses. -/
theorem compactFormalDegree : CompactFormalDegreeStatements.{u, v} :=
  ⟨smoothEndomorphismTensor, compactCoefficientFormalDegree, compactGroupFormalDegree⟩

end Langlands.Renard.CompactRepresentation

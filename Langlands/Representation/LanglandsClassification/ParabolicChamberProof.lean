import Langlands.Representation.LanglandsClassification.ParabolicChamberLinearAlgebraProof
import Langlands.Representation.LanglandsClassification.ParabolicSplitComponentChamberProof

/-! # Assembly of the two published parabolic chamber proofs -/

namespace Langlands.GroupScheme

universe u

/-- Pair the ambient and split-component chamber theorems. -/
theorem parabolicChamber : ParabolicChamberStatement.{u} :=
  ⟨parabolicChamberLinearAlgebra.{u}, parabolicSplitComponentChamber.{u}⟩

end Langlands.GroupScheme

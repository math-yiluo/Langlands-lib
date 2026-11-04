import Langlands.GroupScheme.Rational.SplitTorusVectorLinearizationStatement
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof

/-! # Linearization of split-torus actions on whole vector groups -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- Every split-torus action on a vector group over an algebraically closed field
has natural linear coordinates, with the fixed factor retained. -/
theorem splitTorusVectorLinearization : SplitTorusVectorLinearizationStatement.{u} := by
  intro k _ _ V hV S hS b
  obtain ⟨n, hn⟩ := hV
  obtain ⟨e, he⟩ := torusVectorActionLinearization k S.toGrp V n hS.isTorus hn b
  exact ⟨n, e, he⟩

end Langlands.GroupScheme.RelativeRoot

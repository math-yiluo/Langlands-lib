import Langlands.Representation.Classification.SpehNeighborProductEndpointReduction
import Langlands.Representation.Classification.LanglandsHeadProductSubquotientProof

/-! # The Speh neighbor product at the complementary endpoint -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The irreducible neighboring Speh product occurs in the complementary
endpoint, for the exact supplied equality of total ranks. -/
theorem spehNeighborProductEndpointSubquotient :
    SpehNeighborProductEndpointSubquotient.{uF,uV} F T :=
  spehNeighborProductEndpointSubquotient_of_headProductSubquotient
    (langlandsHeadProductSubquotient.{uF,uV} F T)

end Langlands.Classification

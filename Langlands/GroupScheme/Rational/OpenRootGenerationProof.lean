import Langlands.GroupScheme.Rational.OpenRootGenerationReduction
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof

/-! # Open root and centralizer subgroups generate an open subgroup -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- **KP Corollary 8.2.6** over every nonarchimedean local field: open subgroups
of the actual root groups `U_a(F)` and of `Z(F)` generate an open subgroup of
`G(F)` for the canonical rational-point topology, at every universe. -/
theorem openRootCentralizerGeneration : OpenRootCentralizerGenerationStatement.{u} :=
  openRootCentralizerGeneration_of_dynamicRootOrderedProduct dynamicRootOrderedProduct

end Langlands.GroupScheme.RelativeRoot

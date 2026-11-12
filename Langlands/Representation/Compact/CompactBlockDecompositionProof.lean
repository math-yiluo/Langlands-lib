import Langlands.Representation.Compact.CompactProjectiveInjectiveProof
import Langlands.Representation.Compact.FiniteIsotypicSplittingProof
import Langlands.Representation.Compact.CompactPartDecompositionProof

/-! # Renard IV.1.6–IV.1.7: projectivity, injectivity and compact blocks -/

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- The five assertions of Renard IV.1.6–IV.1.7, with the published objects
and independent group and carrier universes. -/
theorem compactBlockDecomposition : CompactBlockDecompositionStatements.{u, v} :=
  ⟨compactProjectiveInjective, compactPartSemisimple, isotypicSplitting,
    finiteIsotypicSplitting, compactPartDecomposition⟩

end Langlands.Renard.CompactRepresentation

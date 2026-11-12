import Langlands.Representation.CompactCoefficient.CompactProjectionDistributionReduction
import Langlands.Representation.Smooth.RenardHeckeCompletenessReduction
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof

/-! # The compact-representation Hecke projectors: Renard IV.1.5 -/

universe u v

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.5, including uniqueness, refinement, idempotence and conjugation. -/
theorem compactProjectionDistribution :
    CompactProjectionDistributionStatement.{u, v} :=
  compactProjectionDistribution_of_heckeCompleteness.{u, v}
    (Smooth.heckeCompleteness_of_equivalence.{u, v}
      Hecke.heckeNondegenerateModuleEquivalence.{u, u})

end Langlands.Renard.CompactRepresentation

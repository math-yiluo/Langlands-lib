import Langlands.Representation.Exponents.GeneralizedJacquetContractingRangeReduction
import Langlands.Representation.Exponents.SplitComponentOppositeContractionProof

/-! # Renard VI.9.1, Remark 3, from uniform stabilization alone

Renard 2026, VI.9.1, Remarque 3 (printed p.198 / PDF p.204). The published
`GeneralizedJacquetContractingRangeStatement` follows from the Proposition of VI.9.1
(`UniformCompressionStabilizationStatement`) alone: the second antecedent of
`GeneralizedJacquetContractingRangeReductionStatement`, the two-sided contraction
`SplitComponentOppositeContractionStatement` (Renard V.5.2 (iii)), is proved by
`splitComponentOppositeContraction`. The Proposition is not asserted here.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VI.9.1, Remark 3, as an implication with a single antecedent: the uniform
stabilization Proposition of VI.9.1 implies `GeneralizedJacquetContractingRangeStatement`.
The Proposition is not asserted. -/
def GeneralizedJacquetContractingRangeOfStabilizationStatement : Prop :=
  RationalPointFamily.UniformCompressionStabilizationStatement.{u, v} →
    GeneralizedJacquetContractingRangeStatement.{u, v}

/-- `GeneralizedJacquetContractingRangeStatement` (Renard VI.9.1, Remark 3) follows from the
uniform stabilization Proposition of VI.9.1: combine the reduction
`generalizedJacquetContractingRange_of_uniformStabilization` with the proved two-sided
contraction `splitComponentOppositeContraction`. -/
theorem generalizedJacquetContractingRange_of_stabilization :
    GeneralizedJacquetContractingRangeOfStabilizationStatement.{u, v} := fun hstab =>
  generalizedJacquetContractingRange_of_uniformStabilization hstab
    splitComponentOppositeContraction

end Langlands.Aubert.General.RepresentedParabolic

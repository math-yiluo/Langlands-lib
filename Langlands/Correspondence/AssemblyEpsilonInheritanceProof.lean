import Langlands.Correspondence.AssemblyEpsilonClassificationReduction
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationProof
import Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction
import Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof

/-!
# Epsilon-factor inheritance for the assembled correspondence

The two premises left explicit by
`assemblyEpsilonInheritance_of_classification_of_segmentHeadL` are now proved:
the square-integrable Langlands classification and, through JPSS 1983,
Theorem (8.2), the segment-head L-factor formula. Discharging them proves
`AssemblyEpsilonInheritanceStatement` (Henniart 2002, Theorem 1.5(iii),
epsilon part) without hypotheses.
-/

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The assembly of a supercuspidal correspondence inherits pair
epsilon-factor compatibility. -/
theorem assemblyEpsilonInheritance :
    AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F :=
  assemblyEpsilonInheritance_of_classification_of_segmentHeadL F
    (Classification.squareIntegrableLanglandsClassification.{uF, uA}
      F F.canonicalTopologicalData)
    (RankinSelberg.segmentHeadLFactor_of_squareIntegrable.{uF, uA, uA}
      RankinSelberg.squareIntegrableLFactor RankinSelberg.squareIntegrableLFactor)

end Langlands.Correspondence

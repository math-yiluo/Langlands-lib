import Langlands.Representation.Classification.SegmentSocleCriterionAssembly
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Representation.Classification.LinkedSegmentSoclePairReducibleProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof

/-!
# Proof of the segment socle irreducibility criterion

Zelevinsky 1980, Theorem 4.2, for products of segment socles: the assembly
`segmentSocleProductIrreducibility_of_halves` applied to the published proofs of
its three hypotheses.
-/

namespace Langlands.Classification

universe uF uV

/-- Zelevinsky 1980, Theorem 4.2: a product of segment socles is irreducible
exactly when its multisegment is unlinked. -/
theorem segmentSocleProductIrreducibility {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : SegmentSocleProductIrreducibility.{uF, uV} F T :=
  SegmentSocleCriterionAssembly.segmentSocleProductIrreducibility_of_halves F T
    (unlinkedSegmentSocleProductIrreducible F T)
    (linkedSegmentSoclePairReducible F T)
    (twoFactorProductConstituentCommutativity.{uF, max uF uV} F T)

end Langlands.Classification

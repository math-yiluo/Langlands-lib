import Langlands.Representation.Classification.TemperedBlockUniquenessReduction
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.GenericSegmentProductUniquenessProof
import Langlands.Representation.Classification.SquareIntegrableSegmentNonlinkageProof

/-!
# Unordered uniqueness of square-integrable tempered blocks

The analytic segment classification, uniqueness of unlinked special-head
products, and nonlinkage of square-integrable segment heads discharge all three
inputs of the published block-uniqueness reduction.
-/

namespace Langlands.Classification

universe uF uV

/-- Normalized products of irreducible square-integrable unitarizable blocks
are isomorphic exactly when their blocks match, with multiplicity, by a
bijection, equal ranks and actual isomorphisms after rank transport. -/
theorem temperedBlockUniqueness
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TemperedBlockUniqueness.{uF,uV} F T :=
  temperedBlockUniqueness_of_segment_inputs.{uF,uV} F T
    (segmentEssentialSquareIntegrableClassification.{uF,uV} F T)
    (genericSegmentProductUniqueness.{uF,uV} F T)
    (squareIntegrableSegmentNonlinkage.{uF,uV} T)

end Langlands.Classification

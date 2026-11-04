import Langlands.Representation.Aubert.SegmentPolynomialSurjectivity
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof

/-!
# Proof of the segment-polynomial comparison

Zelevinsky 1980, Corollary 7.5: the evaluation of segment polynomials at the actual
graded segment-socle classes is bijective. The argument is
`SegmentPolynomialSurjectivity.segmentPolynomialComparison_of_socleExhaustion`, applied
to the published multisegment socle exhaustion (Zelevinsky 1980, Theorem 6.1 (c)).
-/

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- **Ze80 Corollary 7.5.** The segment-polynomial evaluation
`segmentPolynomialEvaluation F T hx hl` is bijective. -/
theorem segmentPolynomialComparison : SegmentPolynomialComparisonStatement F T hx hl :=
  SegmentPolynomialSurjectivity.segmentPolynomialComparison_of_socleExhaustion F T hx hl
    (Classification.multisegmentSocleExhaustion F T)

end Langlands.Aubert

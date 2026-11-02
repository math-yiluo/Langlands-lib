import Langlands.Representation.Classification.SegmentHeadSupportStep
import Langlands.Representation.Classification.SegmentHeadDerivativeSupportLengthTwo

/-!
# Support bound for derivatives of supplied special heads: proof

Every irreducible actual subquotient of every derivative of a supplied special
head of a segment `Δ` has a supercuspidal support whose set is the support of an
optional terminal truncation of `Δ`. Segments of length one and two are treated
in `SegmentHeadDerivativeSupportLengthTwo`; longer segments by the induction of
`SegmentHeadSupportStep`.
-/

namespace Langlands.Classification

universe uF uV

/-- Proof of `SegmentHeadDerivativeSupportTruncation`. -/
theorem segmentHeadDerivativeSupportTruncation {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentHeadDerivativeSupportTruncation.{uF, uV} F T :=
  SegmentHeadSupport.supportTruncation_of_base T
    (fun Δ hΔ ψ π hπ k hk σ hσ hsub =>
      SegmentHeadDerivativeSupportLengthTwo.lengthOne_support F T ψ Δ hΔ π hπ k hk σ hσ hsub)
    (fun Δ hΔ ψ π hπ k hk σ hσ hsub =>
      SegmentHeadDerivativeSupportLengthTwo.lengthTwo_support F T ψ Δ hΔ π hπ k hk σ hσ hsub)

end Langlands.Classification

import Langlands.Representation.Classification.SegmentCuspidalContent

/-!
# Reconstruction of an unlinked multisegment from cuspidal content

This module states injectivity of multiplicity-preserving cuspidal content
on the unlinked multisegments.
-/

namespace Langlands.Classification

universe uF uV

/-- Unlinked multisegments with equal cuspidal content are equal, including
the empty multisegment and all repeated or nested segment occurrences. -/
def UnlinkedCuspidalContentInjectivity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  ∀ (a b : T.Multisegment.{uV, uF}),
    a.IsUnlinked → b.IsUnlinked →
    a.cuspidalContent = b.cuspidalContent → a = b

end Langlands.Classification

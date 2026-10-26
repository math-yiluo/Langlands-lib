import Langlands.Representation.Classification.SegmentProductPermutation

/-!
# Adjacent unlinked segment-socle swaps in a full induced product

The actual-product form of Zelevinsky 1980, Proposition 6.4(1), retaining every
supplied block through the existing permutation of segment-product data.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Swapping adjacent unlinked segment socles preserves the actual full normalized
induced product, with every supplied block carried by the same permutation. -/
def AdjacentUnlinkedSegmentSocleSwap : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
    d.HasSegmentSocles →
    ∀ (j : ℕ) (h : j + 1 < d.length),
      ¬ (d.segments ⟨j, by omega⟩).IsLinked (d.segments ⟨j + 1, h⟩) →
      Nonempty (d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced)

end Langlands.Classification

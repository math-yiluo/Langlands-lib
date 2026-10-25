import Langlands.Representation.Classification.SegmentProductPermutation

/-!
# Adjacent unlinked segment-head swaps in a full induced product

An actual-isomorphism statement for the two supplied adjacent blocks, with all
other blocks retained. Only the swapped pair is required to be unlinked.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Swapping adjacent unlinked segment heads preserves the actual full normalized
induced product. No ordering or global pairwise nonlinkage is assumed. -/
def AdjacentUnlinkedSegmentSwap : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
    d.HasSegmentHeads →
    ∀ (j : ℕ) (h : j + 1 < d.length),
      ¬ (d.segments ⟨j, by omega⟩).IsLinked (d.segments ⟨j + 1, h⟩) →
      let σ := d.shape.adjacentSwap j h
      Nonempty (d.induced ≅
        (T.normalizedProductInductionFunctor (d.shape.permute σ)).obj
          (fun i => d.blocks (σ i)))

end Langlands.Classification

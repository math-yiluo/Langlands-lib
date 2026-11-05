import Langlands.Representation.Classification.AdjacentUnlinkedSegmentSwapStatement
import Langlands.Representation.Classification.AdjacentSegmentSwapLifting
import Langlands.Representation.Classification.TwoSegmentHeadCommutationProof

/-!
# Adjacent unlinked segment-head swaps in a full induced product

Apply independent two-factor commutation to the two supplied adjacent heads,
then lift that isomorphism through the common merged outer product.
-/

namespace Langlands.Classification

open CategoryTheory AdjacentSegmentSwapLifting

universe uF uV

/-- Swapping two adjacent unlinked supplied segment heads preserves the actual
full normalized induced product, without conditions on the other pairs. -/
theorem adjacentUnlinkedSegmentSwap
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    AdjacentUnlinkedSegmentSwap.{uF, uV} F T := by
  let := T.topology
  intro n d hd j h hunlinked σ
  have hlocal :
      ¬ ((mergedFiber d j h).segments
          ⟨0, by rw [mergedFiber_length]; omega⟩).IsLinked
        ((mergedFiber d j h).segments
          ⟨1, by rw [mergedFiber_length]; omega⟩) := by
    rw [mergedFiber_segments_zero, mergedFiber_segments_one]
    exact hunlinked
  have hcommute := twoSegmentHeadCommutation.{uF, uV} F T _ (mergedFiber d j h)
    (mergedFiber_length d j h)
    (directFiber_heads d j h hd (d.shape.adjacentMergeIndex j h)) hlocal
  obtain ⟨e⟩ := lift d j h hcommute
  have he := PadicField.TopologicalData.SegmentProductDatum.permute_induced d σ
  exact ⟨e ≪≫ eqToIso he⟩

end Langlands.Classification

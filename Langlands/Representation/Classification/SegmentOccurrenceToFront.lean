import Langlands.Combinatorics.MoveOccurrenceToFrontProof
import Langlands.Representation.Classification.AdjacentSegmentSwapLifting
import Langlands.Representation.Classification.TwoSegmentHeadCommutationStatement

/-! # Actual transport of one original segment occurrence -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory

universe uF uV

/-- If the supplied two-factor commutation statement holds, an original segment
occurrence unlinked with all its predecessors can be moved to the front of the
actual full induced product. -/
theorem segmentOccurrenceToFront {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hcomm : TwoSegmentHeadCommutation.{uF,uV} F T) :
    letI := T.topology
    ∀ {n : ℕ} (d : T.SegmentProductDatum.{max uF uV,uF} n),
      d.HasSegmentHeads → ∀ i : Fin d.length,
      (∀ j : Fin d.length, j < i → ¬ (d.segments j).IsLinked (d.segments i)) →
      Nonempty (d.induced ≅ (d.permute (Fin.cycleRange i).symm).induced) := by
  classical
  let := T.topology
  intro n d hd i hi
  apply Combinatorics.moveOccurrenceToFront d.length
    (fun e => Nonempty (d.induced ≅ (d.permute e).induced))
    (fun j i => ¬ (d.segments j).IsLinked (d.segments i))
  · exact ⟨Iso.refl _⟩
  · intro e k hk hrel he
    let q := d.permute e
    have hkq : k + 1 < q.length := hk
    have hq : q.HasSegmentHeads := hd.permute e
    have hmerged := hcomm _ (AdjacentSegmentSwapLifting.mergedFiber q k hkq)
      (AdjacentSegmentSwapLifting.mergedFiber_length q k hkq)
      (AdjacentSegmentSwapLifting.directFiber_heads q k hkq hq _)
    have hunlinked :
        ¬ ((AdjacentSegmentSwapLifting.mergedFiber q k hkq).segments
          ⟨0, by have := AdjacentSegmentSwapLifting.mergedFiber_length q k hkq; omega⟩).IsLinked
          ((AdjacentSegmentSwapLifting.mergedFiber q k hkq).segments
            ⟨1, by have := AdjacentSegmentSwapLifting.mergedFiber_length q k hkq; omega⟩) := by
      rw [AdjacentSegmentSwapLifting.mergedFiber_segments_zero,
        AdjacentSegmentSwapLifting.mergedFiber_segments_one]
      exact hrel
    obtain ⟨eswap⟩ := AdjacentSegmentSwapLifting.lift q k hkq (hmerged hunlinked)
    obtain ⟨eprev⟩ := he
    exact ⟨eprev ≪≫ eswap⟩
  · exact hi

end Langlands.Classification

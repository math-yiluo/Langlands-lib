import Langlands.Representation.Classification.AdjacentUnlinkedSegmentSocleSwapStatement
import Langlands.Representation.Classification.TwoSegmentSocleCommutationProof
import Langlands.Representation.Classification.AdjacentSegmentSwapLifting

/-!
# Adjacent unlinked segment-socle swaps in a full induced product

The full-product swap is lifted from the independent two-factor socle commutation through
direct and swapped adjacent regroupings with the common outer shape `adjacentMerge`.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory

universe uF uV

/-- Swapping two adjacent unlinked segment socles in a full normalized product gives an
isomorphic product. -/
theorem adjacentUnlinkedSegmentSocleSwap
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    AdjacentUnlinkedSegmentSocleSwap.{uF, uV} F T := by
  let := T.topology
  intro n d hd j h hu
  refine AdjacentSegmentSwapLifting.lift d j h ?_
  let a := AdjacentSegmentSwapLifting.mergedFiber d j h
  have hl : a.length = 2 := AdjacentSegmentSwapLifting.mergedFiber_length d j h
  have hu' : ¬ (a.segments ⟨0, by omega⟩).IsLinked (a.segments ⟨1, by omega⟩) := by
    rw [AdjacentSegmentSwapLifting.mergedFiber_segments_zero,
      AdjacentSegmentSwapLifting.mergedFiber_segments_one]
    exact hu
  exact twoSegmentSocleCommutation.{uF, uV} F T _ a hl
    (AdjacentSegmentSwapLifting.directFiber_socles d j h hd _) hu'

end Langlands.Classification

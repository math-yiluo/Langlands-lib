import Langlands.Representation.Classification.TwoSegmentHeadCommutationStatement
import Langlands.Representation.Classification.SegmentHeadProductIrreducibilityProof
import Langlands.Representation.Classification.SegmentHeadProductFiniteness
import Langlands.Representation.Parabolic.ContragredientReversal
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof

/-!
# Two unlinked segment heads commute

For two segments, swapping the two blocks is the reversal of the block order.
Both orders of a pair of unlinked special segment heads give irreducible
products by the segment-head irreducibility criterion, so the
Gelfand–Kazhdan contragredient reversal identifies them.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

/-- In a family of segments whose pairs are all unlinked, the multisegment is
unlinked. -/
theorem multisegment_isUnlinked_of_pairwise {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {T : F.TopologicalData} {n : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} n)
    (h : ∀ i j, ¬ (d.segments i).IsLinked (d.segments j)) :
    d.multisegment.IsUnlinked := by
  intro Δ₁ hΔ₁ Δ₂ hΔ₂
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hΔ₁)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (Multiset.mem_coe.mp hΔ₂)
  exact h i j

/-- Two actual special-head blocks of unlinked segments commute under
normalized product induction. -/
theorem twoSegmentHeadCommutation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSegmentHeadCommutation.{uF, uV} F T := by
  let := T.topology
  have hIrr := segmentHeadProductIrreducibility.{uF, max uF uV} F T
  intro n d h₂ hheads hunl σ
  -- For two blocks the adjacent swap is the reversal of the block order.
  have h₂' : d.shape.length = 2 := h₂
  have hσ : σ = Fin.revPerm := by
    ext ⟨k, hk⟩
    rw [Fin.revPerm_apply, Fin.val_rev]
    change (Equiv.swap (⟨0, by omega⟩ : Fin d.length) ⟨0 + 1, by omega⟩ ⟨k, hk⟩).val = _
    rcases k with _ | _ | k
    · rw [Equiv.swap_apply_left]
      simp only
      omega
    · rw [Equiv.swap_apply_right]
      simp only
      omega
    · omega
  rw [hσ]
  -- The pairs of segments are unlinked.
  have hpair : ∀ i j : Fin d.length, ¬ (d.segments i).IsLinked (d.segments j) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · exact PadicField.TopologicalData.Segment.not_isLinked_self _
      · exact hunl
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · exact fun h => hunl h.symm
      · exact PadicField.TopologicalData.Segment.not_isLinked_self _
  -- The ambient rank is positive.
  have hn : 0 < n := by
    rw [← d.degree_sum]
    exact Finset.sum_pos (fun i _ => (d.segments i).degree_pos)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Both orders give irreducible products.
  have hP : Representation.IsIrreducible d.induced.representation :=
    (hIrr m d hheads).mpr (multisegment_isUnlinked_of_pairwise d hpair)
  have hP' : Representation.IsIrreducible (d.permute Fin.revPerm).induced.representation :=
    (hIrr m (d.permute Fin.revPerm) (hheads.permute Fin.revPerm)).mpr
      (multisegment_isUnlinked_of_pairwise _ fun i j => hpair (Fin.revPerm i) (Fin.revPerm j))
  have hadm : ∀ i, IsAdmissible (d.blocks i).representation :=
    fun i => (hheads i).isAdmissible
  have hirr : ∀ i, Representation.IsIrreducible (d.blocks i).representation :=
    fun i => (hheads i).isIrreducible
  have hP'' := hP'
  rw [PadicField.TopologicalData.SegmentProductDatum.permute_induced] at hP''
  -- Contragredient reversal identifies the two products.
  obtain ⟨E⟩ := Parabolic.normalizedProductInduced_revPerm_equiv T
    gelfandKazhdanContragredient.{uF, max uF uV} gelfandKazhdanContragredient.{uF, max uF uV}
    Parabolic.naturalNormalizedInductionDuality.{uF, max uF uV}.1
    (Nat.succ_pos m) d.shape (fun i => (d.blocks i).representation) hadm hirr hP hP''
  exact ⟨SmoothRep.mkIso E⟩

end Langlands.Classification

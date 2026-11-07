import Langlands.Algebra.MultisetOfFn
import Langlands.Representation.Classification.CuspidalScalarNorm
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Geometric.PieceHom

/-! Matching rank-one segment factors to a weakly norm-ordered target. -/

noncomputable section

namespace Langlands.Classification.RankOneSegmentMatching

open GeneralLinear Geometric PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The segment member at a coordinate of the segment-product shape. For
rank-one segments these coordinates enumerate exactly the cuspidal content. -/
def coordinateMember {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (a : Fin n) : CuspidalDatum.{uV, uF} T :=
  (d.segments (d.shape.indexEquiv.symm a).1).member
    ((d.shape.indexEquiv.symm a).2 : ℕ)

@[simp]
theorem coordinateMember_index {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (j : Fin d.shape.length) (i : Fin (d.shape.size j)) :
    coordinateMember d (d.shape.index j i) = (d.segments j).member (i : ℕ) := by
  change (d.segments (d.shape.indexEquiv.symm (d.shape.indexEquiv ⟨j, i⟩)).1).member
    ((d.shape.indexEquiv.symm (d.shape.indexEquiv ⟨j, i⟩)).2 : ℕ) = _
  rw [Equiv.symm_apply_apply]

/-- Flattening rank-one segment members retains all cuspidal occurrences. -/
theorem coordinateMember_content {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (hrank : ∀ j, (d.segments j).rank = 1) :
    (List.ofFn (coordinateMember d) : Multiset _) = d.multisegment.cuspidalContent := by
  rw [SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum, ← d.shape.indexEquiv.sum_comp, Fintype.sum_sigma]
  change (∑ j, ∑ i, {coordinateMember d (d.shape.index j i)}) = _
  simp only [coordinateMember_index]
  change _ = ((List.ofFn d.segments : Multiset (Segment.{uV, uF} T)).map
    Segment.cuspidalContent).sum
  simp only [Multiset.map_coe, List.map_ofFn, Function.comp_def,
    Multiset.sum_coe, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  rw [Segment.cuspidalContent, SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum]
  have hsize : d.shape.size j = (d.segments j).length := by
    change (d.segments j).length * (d.segments j).rank = _
    rw [hrank j, Nat.mul_one]
  exact (finCongr hsize).sum_comp (fun i => ({(d.segments j).member (i : ℕ)} : Multiset _))

/-- Equal cuspidal content and weakly decreasing scalar-uniformizer norms of
the target give a minimal matching of all increasing rank-one segment factors.
Repeated target values and equal norms are allowed. -/
theorem exists_minimal_matching {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n)
    (hrank : ∀ j, (d.segments j).rank = 1)
    (C : BlockShape n) (hC : ∀ j, C.size j = 1)
    (target : Fin n → CuspidalDatum.{uV, uF} T)
    (hcontent : d.multisegment.cuspidalContent = List.ofFn target)
    (htarget : Antitone (fun i => (target i).scalarUniformizerNorm)) :
    ∃ w : MinimalRepresentatives d.shape C,
      ∀ j (i : Fin (d.shape.size j)),
        (d.segments j).member (i : ℕ) = target (w.val (d.shape.index j i)) := by
  obtain ⟨w, hw⟩ := exists_minimal_matching_of_sorted (β := OrderDual ℝ) d.shape C hC
    (coordinateMember d) target
    (fun ρ => (ρ.scalarUniformizerNorm : OrderDual ℝ))
    ((coordinateMember_content d hrank).trans hcontent) (by
      intro j a b hab
      change (coordinateMember d (d.shape.index j b)).scalarUniformizerNorm <
        (coordinateMember d (d.shape.index j a)).scalarUniformizerNorm
      rw [coordinateMember_index, coordinateMember_index]
      exact (d.segments j).base.strictAnti_scalarUniformizerNorm_twist
        (by exact_mod_cast hab)) htarget
  exact ⟨w, fun j i => (coordinateMember_index d j i).symm.trans (hw _)⟩

end Langlands.Classification.RankOneSegmentMatching

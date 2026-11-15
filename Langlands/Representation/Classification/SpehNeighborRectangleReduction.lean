import Langlands.Representation.Classification.SpehNeighborProductAssembly
import Langlands.Representation.Classification.SpehMultisegmentAdapters
import Langlands.Representation.Classification.SpehUnitarizabilityReductionStatement

/-! # Reduction of the exact Speh neighbor target to a rectangle length bound -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Classification.SpehNeighborProduct

open PadicField.TopologicalData SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The outstanding constituent-length bound, stated for actual heads of the
two centered neighboring rectangles. This definition asserts no proof. -/
def NeighborRectangleConstituentLengthBound : Prop :=
  letI := T.topology
  ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}) (k l : ℕ)
    (hl : 0 < l) (_hk : 2 ≤ k) (m n : ℕ)
    (dA : T.SegmentProductDatum.{max uF uV, uF} m)
    (dB : T.SegmentProductDatum.{max uF uV, uF} n),
    dA.multisegment = tadicMultisegment ρ (k + 1) l hl →
    dB.multisegment = tadicMultisegment ρ (k - 1) l hl →
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      dA.IsLanglandsQuotient A → dB.IsLanglandsQuotient B →
      ∀ (dC : T.SegmentProductDatum.{max uF uV, uF} (m + n))
        (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
        dC.IsLanglandsQuotient C →
        IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
        ∀ Δ ∈ dC.multisegment, Δ.length ≤ l

/-- Every member of a centered rectangle has its prescribed segment length. -/
theorem length_eq_of_mem_tadicMultisegment
    (ρ : T.CuspidalDatum.{max uF uV, uF}) (k l : ℕ) (hl : 0 < l)
    (Δ : T.Segment.{max uF uV, uF}) (hΔ : Δ ∈ tadicMultisegment ρ k l hl) :
    Δ.length = l := by
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hΔ
  rfl

/-- The published head-product proposition and the rectangle bound suffice
for the exact published neighboring Speh irreducibility proposition, with its
original universes and actual positive-rank normalized product. -/
theorem spehNeighborProductIrreducibility_of_rectangle_bound
    (hH : Aubert.HeadProductLeadingTermStatement.{uF, uV} F T)
    (hbound : NeighborRectangleConstituentLengthBound.{uF, uV} F T) :
    SpehNeighborProductIrreducibility.{uF, uV} F T := by
  let := T.topology
  intro d hk hd Sup Sdown hsup hdown
  obtain ⟨Δ, hΔ, hδ⟩ := d.exists_segmentHead hd
  let dup := d.withLength (d.length + 1) (Nat.succ_pos _)
  let ddown := d.withLength (d.length - 1) (Nat.sub_pos_of_lt hk)
  let dA := dup.segmentProductDatum Δ hΔ
  let dB := ddown.segmentProductDatum Δ hΔ
  have hA : dA.IsLanglandsQuotient Sup :=
    dup.isLanglandsQuotient_segmentProductDatum Δ hΔ hδ Sup hsup
  have hB : dB.IsLanglandsQuotient Sdown :=
    ddown.isLanglandsQuotient_segmentProductDatum Δ hΔ hδ Sdown hdown
  let ρ := Δ.base.twist (((Δ.length : ℝ) - 1) / 2)
  have hlabelA : dA.multisegment = tadicMultisegment ρ (d.length + 1) Δ.length Δ.length_pos :=
    dup.segmentProductDatum_centered_multisegment Δ hΔ
  have hlabelB : dB.multisegment = tadicMultisegment ρ (d.length - 1) Δ.length Δ.length_pos :=
    ddown.segmentProductDatum_centered_multisegment Δ hΔ
  rw [← T.binaryNormalizedProductFunctor_of_pos
    (Nat.mul_pos (Nat.succ_pos d.length) d.rank_pos)
    (Nat.mul_pos (Nat.sub_pos_of_lt hk) d.rank_pos)]
  refine isIrreducible_of_constituent_segment_length_le F T hH
    (l := Δ.length) dA dB Sup Sdown hA hB ?_ ?_
  · intro Γ hΓ
    rw [hlabelA, hlabelB] at hΓ
    rcases Multiset.mem_add.mp hΓ with hΓ | hΓ
    · exact length_eq_of_mem_tadicMultisegment F T ρ _ _ _ Γ hΓ
    · exact length_eq_of_mem_tadicMultisegment F T ρ _ _ _ Γ hΓ
  · intro dC C hC hsub
    exact hbound ρ d.length Δ.length Δ.length_pos hk _ _ dA dB
      hlabelA hlabelB Sup Sdown hA hB dC C hC hsub

end Langlands.Classification.SpehNeighborProduct

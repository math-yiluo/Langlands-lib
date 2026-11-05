import Langlands.Representation.Classification.SegmentProductReplacement
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof

/-! Actual special-head data and exact cuspidal content for a linked replacement. -/

noncomputable section

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- Integral twist freeness makes the indexed cuspidal content repetition-free
inside a single segment. Repeated segment occurrences are still retained. -/
theorem cuspidalContent_nodup_of_twistFreeness
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF,uV} F T)
    (Δ : Segment.{uV,uF} T) : Δ.cuspidalContent.Nodup := by
  change (List.ofFn (fun i : Fin Δ.length => Δ.member (i : ℕ))).Nodup
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  have h : (i.val : ℤ) = (j.val : ℤ) :=
    Δ.base.integralTwist_injective hfree
      (by simpa only [member, Int.cast_natCast] using hij)
  exact_mod_cast h

/-- The replacement preserves every cuspidal multiplicity, including those
members lying in both original segments. -/
theorem IsUnionIntersectionReplacement.cuspidalContent_sum
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF,uV} F T)
    {Δ Γ U : Segment.{uV,uF} T} {I : Option (Segment.{uV,uF} T)}
    (hs : IsUnionIntersectionReplacement Δ Γ U I) :
    U.cuspidalContent + (I.toList.map Segment.cuspidalContent).sum =
      Δ.cuspidalContent + Γ.cuspidalContent := by
  classical
  apply Multiset.ext.mpr
  intro ρ
  have hΔ := Δ.cuspidalContent_nodup_of_twistFreeness hfree
  have hΓ := Γ.cuspidalContent_nodup_of_twistFreeness hfree
  have hU := U.cuspidalContent_nodup_of_twistFreeness hfree
  cases I with
  | none =>
    have hI : Δ.support ∩ Γ.support = ∅ := hs.2
    have hUnion : ρ ∈ U.support ↔ ρ ∈ Δ.support ∨ ρ ∈ Γ.support := by
      rw [hs.1, Set.mem_union]
    have hDisj : ¬ (ρ ∈ Δ.support ∧ ρ ∈ Γ.support) := by
      intro h
      have : ρ ∈ Δ.support ∩ Γ.support := h
      rw [hI] at this
      exact this
    simp only [Option.toList_none, List.map_nil, List.sum_nil,
      Multiset.add_zero, Multiset.count_add,
      Multiset.count_eq_of_nodup hΔ, Multiset.count_eq_of_nodup hΓ,
      Multiset.count_eq_of_nodup hU, mem_cuspidalContent]
    split_ifs <;> simp_all
  | some J =>
    have hJ := J.cuspidalContent_nodup_of_twistFreeness hfree
    have hUnion : ρ ∈ U.support ↔ ρ ∈ Δ.support ∨ ρ ∈ Γ.support := by
      rw [hs.1, Set.mem_union]
    have hInter : ρ ∈ J.support ↔ ρ ∈ Δ.support ∧ ρ ∈ Γ.support := by
      rw [hs.2, Set.mem_inter_iff]
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, Multiset.count_add,
      Multiset.count_eq_of_nodup hΔ, Multiset.count_eq_of_nodup hΓ,
      Multiset.count_eq_of_nodup hU, Multiset.count_eq_of_nodup hJ,
      mem_cuspidalContent]
    split_ifs <;> simp_all

end Segment

namespace SegmentProductDatum

/-- The actual head condition for a block list is precisely the pointwise
head condition for its associated datum. -/
theorem ofBlockList_hasSegmentHeads_iff {n : ℕ}
    (l : List (SegmentBlock.{uF,uV} T))
    (h : (l.map fun b => b.1.degree).sum = n) :
    (ofBlockList l h).HasSegmentHeads ↔ ∀ b ∈ l, T.IsSegmentHead b.1 b.2 := by
  simp only [HasSegmentHeads, ofBlockList]
  exact (List.forall_mem_iff_get (l := l)
    (p := fun b : SegmentBlock.{uF,uV} T => T.IsSegmentHead b.1 b.2)).symm

end SegmentProductDatum

end Langlands.PadicField.TopologicalData

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- Choose actual individual special heads for a complete occurrence list,
without changing its rank, order, or multiplicities. -/
def segmentHeadDatumOfList {n : ℕ} (l : List (Segment.{uV,uF} T))
    (h : (l.map Segment.degree).sum = n) :
    {d : T.SegmentProductDatum.{uV,uF} n //
      d.HasSegmentHeads ∧ List.ofFn d.segments = l} := by
  letI := T.topology
  let H (Δ : Segment.{uV,uF} T) := Classical.choose
    (segmentSpecialConstituentExistence F T Δ)
  have hH (Δ : Segment.{uV,uF} T) : T.IsSegmentHead Δ (H Δ) :=
    (Classical.choose_spec (segmentSpecialConstituentExistence F T Δ)).1
  let blocks : List (SegmentBlock.{uF,uV} T) := l.map fun Δ => ⟨Δ,H Δ⟩
  have hdeg : (blocks.map fun b => b.1.degree).sum = n := by
    simpa only [blocks, List.map_map, Function.comp_def] using h
  refine ⟨SegmentProductDatum.ofBlockList blocks hdeg, ?_, ?_⟩
  · rw [SegmentProductDatum.ofBlockList_hasSegmentHeads_iff]
    intro b hb
    obtain ⟨Δ,_,rfl⟩ := List.mem_map.mp hb
    exact hH Δ
  · rw [SegmentProductDatum.ofBlockList_segments]
    simp only [blocks, List.map_map, Function.comp_def]
    change l.map id = l
    exact List.map_id l

/-- Actual replacement data on the original rank, with an exact cuspidal
multiset identity and the union followed by its optional intersection. -/
structure SegmentHeadReplacementDatum
    (Δ Γ U : T.Segment.{uV,uF}) (I : Option (T.Segment.{uV,uF})) where
  datum : T.SegmentProductDatum.{uV,uF} (Δ.degree+Γ.degree)
  heads : datum.HasSegmentHeads
  segments : List.ofFn datum.segments = U :: I.toList
  content : datum.multisegment.cuspidalContent =
    Δ.cuspidalContent + Γ.cuspidalContent

/-- Construct actual replacement heads and retain every cuspidal multiplicity. -/
def segmentHeadReplacementDatum
    (hfree : CuspidalIntegralTwistFreeness.{uF,uV} F T)
    {Δ Γ U : T.Segment.{uV,uF}} {I : Option (T.Segment.{uV,uF})}
    (hp : Δ.Precedes Γ) (hs : Segment.IsUnionIntersectionReplacement Δ Γ U I) :
    SegmentHeadReplacementDatum T Δ Γ U I := by
  have hdeg : ((U :: I.toList).map Segment.degree).sum = Δ.degree+Γ.degree := by
    simpa only [List.map_cons, List.sum_cons] using hs.degree_sum hfree hp
  let d := segmentHeadDatumOfList T (U :: I.toList) hdeg
  refine ⟨d.val,d.property.1,d.property.2,?_⟩
  change Multisegment.cuspidalContent
    (List.ofFn d.val.segments : Multiset (T.Segment.{uV,uF})) = _
  rw [d.property.2]
  simpa only [Multisegment.cuspidalContent, Multiset.map_coe, Multiset.sum_coe,
    List.map_cons, List.sum_cons] using
      hs.cuspidalContent_sum hfree

end Langlands.Classification

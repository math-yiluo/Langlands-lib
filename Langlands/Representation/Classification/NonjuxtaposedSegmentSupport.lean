import Langlands.Representation.Classification.SegmentContentShift

/-!
# The support obstruction for nonjuxtaposed segments

This is finite multiset bookkeeping. A Boolean records whether each segment
has lost its last member. If the positive unit twist of the residual content
is contained in the original content, every segment has been shortened.
-/

noncomputable section

namespace Langlands.Classification.NonjuxtaposedSegmentSupport

open PadicField.TopologicalData
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- The full segment content, or its content after removing its final member.
A shortened singleton contributes the empty multiset. -/
def residualContent (Δ : T.Segment.{uV, uF}) (shorten : Bool) :
    Multiset T.CuspidalDatum.{uV, uF} :=
  if shorten then
    ((SegmentContentShift.lower Δ).map Segment.cuspidalContent).getD 0
  else Δ.cuspidalContent

/-- Sum the residual contents over all positions, retaining multiplicities. -/
def content {r : ℕ} (segments : Fin r → T.Segment.{uV, uF})
    (shorten : Fin r → Bool) : Multiset T.CuspidalDatum.{uV, uF} :=
  ∑ i, residualContent (segments i) (shorten i)

@[simp]
theorem residualContent_false (Δ : T.Segment.{uV, uF}) :
    residualContent Δ false = Δ.cuspidalContent := rfl

theorem residualContent_true_of_two_le (Δ : T.Segment.{uV, uF})
    (h : 2 ≤ Δ.length) :
    residualContent Δ true =
      (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF}).cuspidalContent := by
  simp [residualContent, SegmentContentShift.lower, h]

theorem residualContent_true_of_length_one (Δ : T.Segment.{uV, uF})
    (h : Δ.length = 1) : residualContent Δ true = 0 := by
  simp [residualContent, SegmentContentShift.lower, h]

/-- The residual shift identity for one segment. -/
theorem residualContent_map_twist_add_base (Δ : T.Segment.{uV, uF})
    (shorten : Bool) :
    (residualContent Δ shorten).map (CuspidalDatum.twist 1) + {Δ.base} =
      Δ.cuspidalContent + if shorten then 0 else {Δ.last.twist 1} := by
  cases shorten with
  | false => exact SegmentContentShift.content_map_twist_add_base Δ
  | true =>
    by_cases h : 2 ≤ Δ.length
    · simpa only [residualContent_true_of_two_le Δ h, Bool.false_eq_true,
        ↓reduceIte, add_zero] using SegmentContentShift.lower_content Δ h
    · have h1 : Δ.length = 1 := by have := Δ.length_pos; omega
      simp [residualContent_true_of_length_one Δ h1, Δ.cuspidalContent_of_length_one h1]

/-- Summing the residual shift identities leaves precisely the shifted ends of
the unshortened positions. -/
theorem content_map_twist_add_bases {r : ℕ}
    (segments : Fin r → T.Segment.{uV, uF}) (shorten : Fin r → Bool) :
    (content segments shorten).map (CuspidalDatum.twist 1) +
        (∑ i, ({(segments i).base} : Multiset T.CuspidalDatum.{uV, uF})) =
      (∑ i, (segments i).cuspidalContent) +
        ∑ i, if shorten i then 0 else {(segments i).last.twist 1} := by
  have hmap :
      (content segments shorten).map (CuspidalDatum.twist 1) =
        ∑ i, (residualContent (segments i) (shorten i)).map (CuspidalDatum.twist 1) := by
    exact map_sum (Multiset.mapAddMonoidHom (CuspidalDatum.twist 1)) _ _
  rw [hmap, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => residualContent_map_twist_add_base _ _

/-- An unshortened position forces its shifted end to be a segment beginning. -/
theorem exists_base_eq_last_twist {r : ℕ}
    (segments : Fin r → T.Segment.{uV, uF}) (shorten : Fin r → Bool)
    (h : (content segments shorten).map (CuspidalDatum.twist 1) ≤
      ∑ i, (segments i).cuspidalContent)
    (i : Fin r) (hi : shorten i = false) :
    ∃ j : Fin r, (segments j).base = (segments i).last.twist 1 := by
  have hle :
      (∑ j, (if shorten j then 0 else
        ({(segments j).last.twist 1} : Multiset T.CuspidalDatum.{uV, uF}))) ≤
      ∑ j, ({(segments j).base} : Multiset T.CuspidalDatum.{uV, uF}) := by
    apply le_of_add_le_add_left (a := ∑ j, (segments j).cuspidalContent)
    rw [← content_map_twist_add_bases]
    exact add_le_add h le_rfl
  have hend :
      ({(segments i).last.twist 1} : Multiset T.CuspidalDatum.{uV, uF}) ≤
      ∑ j, ({(segments j).base} : Multiset T.CuspidalDatum.{uV, uF}) := by
    apply le_trans _ hle
    have hs := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
        (show 0 ≤ if shorten j then 0 else
          ({(segments j).last.twist 1} : Multiset T.CuspidalDatum.{uV, uF}) from zero_le))
      (Finset.mem_univ i)
    simpa only [hi, Bool.false_eq_true, ↓reduceIte] using hs
  obtain ⟨j, _, hj⟩ := Multiset.mem_sum.mp (Multiset.singleton_le.mp hend)
  exact ⟨j, (Multiset.mem_singleton.mp hj).symm⟩

/-- Adjacent endpoints on a free integral twist line give actual juxtaposition,
including disjointness of the supports. -/
theorem isJuxtaposed_of_base_eq_last_twist
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {Δ Γ : T.Segment.{uV, uF}} (hbase : Γ.base = Δ.last.twist 1) :
    Δ.IsJuxtaposed Γ := by
  have hlast : Δ.last.twist 1 = Δ.base.twist (Δ.length : ℝ) := by
    rw [Segment.last, Segment.member, CuspidalDatum.twist_twist]
    congr 1
    have := Δ.length_pos
    push_cast [Nat.cast_sub (by omega : 1 ≤ Δ.length)]
    ring
  have hinj : Function.Injective Δ.member := by
    intro a b hab
    have he := congrArg (fun ρ : T.CuspidalDatum.{uV, uF} => ρ.twist (-(b : ℝ))) hab
    have ht : Δ.base.twist (((a : ℤ) - b : ℤ) : ℝ) = Δ.base := by
      simpa only [Segment.member, CuspidalDatum.twist_twist, neg_add_cancel,
        CuspidalDatum.twist_zero, Int.cast_sub, Int.cast_natCast, neg_add_eq_sub] using he
    have hz := (hfree Δ.base ((a : ℤ) - b)).mp ht
    omega
  have hΓmember : ∀ j : ℕ, Γ.member j = Δ.member (Δ.length + j) := by
    intro j
    rw [Segment.member, hbase, hlast, CuspidalDatum.twist_twist, Segment.member,
      Nat.cast_add, add_comm]
  have hd : Disjoint Δ.support Γ.support := by
    apply Set.disjoint_left.mpr
    intro σ hσΔ hσΓ
    obtain ⟨i, hi, hσi⟩ := hσΔ
    obtain ⟨j, _, hσj⟩ := hσΓ
    have hij : i = Δ.length + j := hinj (hσi.trans (hσj.symm.trans (hΓmember j)))
    omega
  let U : T.Segment.{uV, uF} :=
    ⟨Δ.base, Δ.length + Γ.length, by have := Δ.length_pos; omega⟩
  have hU : U.support = Δ.support ∪ Γ.support := by
    ext σ
    constructor
    · rintro ⟨i, hi, rfl⟩
      change i < Δ.length + Γ.length at hi
      by_cases hiΔ : i < Δ.length
      · exact Or.inl ⟨i, hiΔ, rfl⟩
      · refine Or.inr ⟨i - Δ.length, by omega, ?_⟩
        rw [hΓmember]
        have he : Δ.length + (i - Δ.length) = i := by omega
        rw [he]
        rfl
    · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨i, by change i < Δ.length + Γ.length; omega, rfl⟩
      · exact ⟨Δ.length + j, by change Δ.length + j < Δ.length + Γ.length; omega,
          (hΓmember j).symm⟩
  refine ⟨⟨?_, ?_, ⟨U, hU⟩⟩, hd⟩
  · intro hs
    exact Set.disjoint_left.mp hd Δ.base_mem_support (hs Δ.base_mem_support)
  · intro hs
    exact Set.disjoint_left.mp hd (hs Γ.base_mem_support) Γ.base_mem_support

/-- The finite-support obstruction used in Zelevinsky's Proposition 4.3:
positive-twist support containment forces every position to be shortened. -/
theorem all_shortened_of_map_twist_le
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {r : ℕ} (segments : Fin r → T.Segment.{uV, uF}) (shorten : Fin r → Bool)
    (hsep : ∀ i j, i ≠ j → ¬ (segments i).IsJuxtaposed (segments j))
    (h : (content segments shorten).map (CuspidalDatum.twist 1) ≤
      ∑ i, (segments i).cuspidalContent) :
    ∀ i, shorten i = true := by
  intro i
  cases hi : shorten i with
  | true => rfl
  | false =>
    obtain ⟨j, hj⟩ := exists_base_eq_last_twist segments shorten h i hi
    by_cases hij : i = j
    · subst j
      exact (SegmentContentShift.base_ne_last_twist hfree (segments i) hj).elim
    · exact (hsep i j hij (isJuxtaposed_of_base_eq_last_twist hfree hj)).elim

/-- With each selected order either zero or its segment's rank, support
containment forces the sum of orders to be the sum of segment ranks. -/
theorem sum_orders_eq_sum_ranks
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    {r : ℕ} (segments : Fin r → T.Segment.{uV, uF}) (shorten : Fin r → Bool)
    (hsep : ∀ i j, i ≠ j → ¬ (segments i).IsJuxtaposed (segments j))
    (h : (content segments shorten).map (CuspidalDatum.twist 1) ≤
      ∑ i, (segments i).cuspidalContent) :
    (∑ i, if shorten i then (segments i).rank else 0) =
      ∑ i, (segments i).rank := by
  have hall := all_shortened_of_map_twist_le hfree segments shorten hsep h
  simp only [hall, ↓reduceIte]

end Langlands.Classification.NonjuxtaposedSegmentSupport

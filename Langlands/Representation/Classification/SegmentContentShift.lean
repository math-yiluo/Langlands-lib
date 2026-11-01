import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement

/-!
# Shifted cuspidal contents of segments

Multiset bookkeeping for Case 2 of Zelevinsky's Theorem 6.2. Write `Δ⁻` for
the segment `Δ` with its end removed, absent when `Δ` is a singleton. If
`ν · (Δ_1 + Δ_2⁻ + ⋯ + Δ_r⁻) ≤ Δ_1 + Δ_2 + ⋯ + Δ_r` as multisets of cuspidal
data, then `ν · e(Δ_1)` is the beginning of some `Δ_j`. Integral twist
freeness rules out `j = 1`.
-/

noncomputable section

namespace Langlands.Classification.SegmentContentShift

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- `Δ⁻`: the segment with the same beginning and one member fewer, absent for
a singleton. -/
def lower (Δ : T.Segment.{uV, uF}) : Option T.Segment.{uV, uF} :=
  if h : 2 ≤ Δ.length then some (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF})
  else none

private theorem ofFn_twist_map_add (b : T.CuspidalDatum.{uV, uF}) (m : ℕ) :
    ((List.ofFn (fun i : Fin m => b.twist ((i : ℕ) : ℝ)) : Multiset _).map
        (CuspidalDatum.twist 1)) + {b} =
      (List.ofFn (fun i : Fin (m + 1) => b.twist ((i : ℕ) : ℝ)) : Multiset _) := by
  have h : ∀ i : Fin m, (b.twist ((i : ℕ) : ℝ)).twist 1 = b.twist ((i.succ : ℕ) : ℝ) := by
    intro i
    rw [CuspidalDatum.twist_twist, Fin.val_succ, Nat.cast_succ, add_comm]
  rw [List.ofFn_succ, Multiset.map_coe, List.map_ofFn]
  simp only [Function.comp_def, h, Fin.val_zero, Nat.cast_zero, CuspidalDatum.twist_zero]
  rw [← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]

private theorem ofFn_twist_succ (b : T.CuspidalDatum.{uV, uF}) (m : ℕ) :
    (List.ofFn (fun i : Fin (m + 1) => b.twist ((i : ℕ) : ℝ)) : Multiset _) =
      (List.ofFn (fun i : Fin m => b.twist ((i : ℕ) : ℝ)) : Multiset _) +
        {b.twist (m : ℝ)} := by
  rw [List.ofFn_succ', List.concat_eq_append, ← Multiset.coe_add]
  simp

/-- `ν · Δ⁻` together with the beginning of `Δ` is `Δ`. -/
theorem lower_content (Δ : T.Segment.{uV, uF}) (h : 2 ≤ Δ.length) :
    (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF}).cuspidalContent.map
        (CuspidalDatum.twist 1) + {Δ.base} = Δ.cuspidalContent := by
  obtain ⟨b, m, hm⟩ := Δ
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Segment.cuspidalContent, Segment.member, Nat.add_sub_cancel]
  exact ofFn_twist_map_add b m

/-- `ν · Δ` together with the beginning of `Δ` is `Δ` together with `ν · e(Δ)`. -/
theorem content_map_twist_add_base (Δ : T.Segment.{uV, uF}) :
    Δ.cuspidalContent.map (CuspidalDatum.twist 1) + {Δ.base} =
      Δ.cuspidalContent + {Δ.last.twist 1} := by
  obtain ⟨b, m, hm⟩ := Δ
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Segment.cuspidalContent, Segment.last, Segment.member, Nat.add_sub_cancel]
  rw [ofFn_twist_map_add b (m + 1), ofFn_twist_succ b (m + 1), CuspidalDatum.twist_twist,
    Nat.cast_succ, add_comm (1 : ℝ)]

/-- Summed over a list: `ν · ∑ Δ⁻` together with all beginnings is `∑ Δ`. -/
theorem filterMap_lower_content (L : List T.Segment.{uV, uF}) :
    ((L.filterMap lower).map Segment.cuspidalContent).sum.map (CuspidalDatum.twist 1) +
        ((L.map Segment.base : List _) : Multiset _) =
      (L.map Segment.cuspidalContent).sum := by
  induction L with
  | nil => simp
  | cons Δ L ih =>
    by_cases h : 2 ≤ Δ.length
    · have hl : lower Δ = some ⟨Δ.base, Δ.length - 1, by omega⟩ := by
        simp [lower, h]
      rw [List.filterMap_cons_some hl]
      simp only [List.map_cons, List.sum_cons, Multiset.map_add]
      rw [← lower_content Δ h, ← ih, ← Multiset.cons_coe, ← Multiset.singleton_add]
      abel
    · have hl : lower Δ = none := by simp [lower, h]
      rw [List.filterMap_cons_none hl]
      have h1 : Δ.length = 1 := by
        have := Δ.length_pos
        omega
      simp only [List.map_cons, List.sum_cons]
      rw [Δ.cuspidalContent_of_length_one h1, ← ih, ← Multiset.cons_coe,
        ← Multiset.singleton_add]
      abel

/-- If `ν · (Δ_1 + ∑ Δ⁻) ≤ Δ_1 + ∑ Δ`, then `ν · e(Δ_1)` begins one of the
segments. -/
theorem exists_base_eq_last_twist (Δ₁ : T.Segment.{uV, uF}) (L : List T.Segment.{uV, uF})
    (h : (Δ₁.cuspidalContent + ((L.filterMap lower).map Segment.cuspidalContent).sum).map
        (CuspidalDatum.twist 1) ≤ Δ₁.cuspidalContent + (L.map Segment.cuspidalContent).sum) :
    ∃ Δ ∈ Δ₁ :: L, Δ.base = Δ₁.last.twist 1 := by
  have key :
      (Δ₁.cuspidalContent + ((L.filterMap lower).map Segment.cuspidalContent).sum).map
          (CuspidalDatum.twist 1) + (((Δ₁ :: L).map Segment.base : List _) : Multiset _) =
        (Δ₁.cuspidalContent + (L.map Segment.cuspidalContent).sum) +
          {Δ₁.last.twist 1} := by
    rw [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add]
    calc
      _ = (Δ₁.cuspidalContent.map (CuspidalDatum.twist 1) + {Δ₁.base}) +
          (((L.filterMap lower).map Segment.cuspidalContent).sum.map (CuspidalDatum.twist 1) +
            ((L.map Segment.base : List _) : Multiset _)) := by
        rw [Multiset.map_add]
        abel
      _ = _ := by
        rw [content_map_twist_add_base, filterMap_lower_content]
        abel
  have hle : (Δ₁.cuspidalContent + (L.map Segment.cuspidalContent).sum) +
      {Δ₁.last.twist 1} ≤ (Δ₁.cuspidalContent + (L.map Segment.cuspidalContent).sum) +
        (((Δ₁ :: L).map Segment.base : List _) : Multiset _) := by
    rw [← key]
    exact add_le_add_left h _
  have hx := Multiset.singleton_le.mp (le_of_add_le_add_left hle)
  obtain ⟨Δ, hΔ, hb⟩ := List.mem_map.mp (Multiset.mem_coe.mp hx)
  exact ⟨Δ, hΔ, hb⟩

/-- Under integral twist freeness, `ν · e(Δ)` is never the beginning of `Δ`. -/
theorem base_ne_last_twist
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (Δ : T.Segment.{uV, uF}) : Δ.base ≠ Δ.last.twist 1 := by
  intro heq
  have hpos := Δ.length_pos
  have htw : Δ.last.twist 1 = Δ.base.twist ((Δ.length : ℤ) : ℝ) := by
    rw [Segment.last, Segment.member, CuspidalDatum.twist_twist]
    congr 1
    push_cast [Nat.cast_sub hpos]
    ring
  have hz := (hfree Δ.base Δ.length).mp (htw.symm.trans heq.symm)
  omega

/-- Case 2 bookkeeping: under twist freeness and the endpoint condition for the
later segments, `ν · (Δ_1 + ∑ Δ⁻)` is not contained in `Δ_1 + ∑ Δ`. -/
theorem not_map_twist_le
    (hfree : Classification.CuspidalIntegralTwistFreeness.{uF, uV} F T)
    (Δ₁ : T.Segment.{uV, uF}) (L : List T.Segment.{uV, uF})
    (hsep : ∀ Δ ∈ L, Δ.base ≠ Δ₁.last.twist 1) :
    ¬ (Δ₁.cuspidalContent + ((L.filterMap lower).map Segment.cuspidalContent).sum).map
        (CuspidalDatum.twist 1) ≤ Δ₁.cuspidalContent + (L.map Segment.cuspidalContent).sum := by
  intro h
  obtain ⟨Δ, hΔ, hb⟩ := exists_base_eq_last_twist Δ₁ L h
  rcases List.mem_cons.mp hΔ with rfl | hΔ
  · exact base_ne_last_twist hfree Δ hb
  · exact hsep Δ hΔ hb

end Langlands.Classification.SegmentContentShift

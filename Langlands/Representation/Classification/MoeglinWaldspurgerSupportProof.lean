import Langlands.Representation.Classification.MoeglinWaldspurgerStatements

/-! # Support preservation for the integer-line MW recursion -/

namespace Langlands.MoeglinWaldspurger

@[simp] theorem support_zero : support 0 = 0 := rfl

@[simp] theorem support_cons (I : Interval) (a : Multisegment) :
    support (I ::ₘ a) = I.support + support a := by
  simp [support]

@[simp] theorem support_add (a b : Multisegment) :
    support (a + b) = support a + support b := by
  simp [support]

/-- Shortening one occurrence removes exactly its right endpoint. -/
theorem support_dropLast_add_ending (I : Interval) :
    support I.dropLast + {I.ending} = I.support := by
  rcases I with ⟨b, e, hbe⟩
  by_cases h : b < e
  · have hn : (e - b).toNat = (e - 1 - b).toNat + 1 := by omega
    have he : b + ((e - b).toNat : ℤ) = e := by omega
    simp only [Interval.dropLast, h, ↓reduceDIte, support, Multiset.singleton_bind,
      Interval.support, Interval.length]
    have he' : b + (((e - 1 - b).toNat + 1 : ℕ) : ℤ) = e := by
      rw [← hn]
      exact he
    conv_rhs => rw [hn, Multiset.range_succ, Multiset.map_cons, he']
    rw [← Multiset.singleton_add]
    exact Multiset.add_comm _ _
  · have he : e = b := by omega
    subst e
    simp [Interval.dropLast, Interval.support, Interval.length, support]

/-- For a multiset of selected occurrences, the removed points are its endings,
with multiplicity. -/
theorem support_shorten_add_endings (a : Multisegment) :
    support (shorten a) + endings a = support a := by
  induction a using Multiset.induction_on with
  | empty => simp [shorten, endings]
  | cons I a ih =>
    have hc : shorten (I ::ₘ a) = I.dropLast + shorten a := by
      simp [shorten]
    have he : endings (I ::ₘ a) = {I.ending} + endings a := by
      simp [endings]
    rw [hc, support_add, he, support_cons]
    calc
      _ = (support I.dropLast + {I.ending}) +
          (support (shorten a) + endings a) := by ac_rfl
      _ = _ := by rw [support_dropLast_add_ending, ih]

/-- The multiset of a list of consecutive descending endings is the same
integer interval listed in ascending order. -/
theorem endings_of_consecutive (l : List Interval) (e : ℤ)
    (h : ∀ (i : ℕ) (hi : i < l.length), (l[i]).ending = e - (i : ℤ)) :
    (l : Multisegment).map Interval.ending =
      (Multiset.range l.length).map
        (fun i : ℕ => e - (l.length : ℤ) + 1 + (i : ℤ)) := by
  induction l generalizing e with
  | nil => simp
  | cons I l ih =>
    have hI : I.ending = e := by
      have hh := h 0 (by simp)
      change I.ending = e - 0 at hh
      simpa only [sub_zero] using hh
    have hl : ∀ (i : ℕ) (hi : i < l.length),
        (l[i]).ending = (e - 1) - (i : ℤ) := by
      intro i hi
      have hh := h (i + 1) (by simpa using hi)
      simpa only [List.getElem_cons_succ] using hh.trans (by push_cast; ring)
    rw [← Multiset.cons_coe, Multiset.map_cons, hI, ih (e - 1) hl]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
      Multiset.range_succ, Multiset.map_cons]
    congr 1
    · ring
    · apply Multiset.map_congr rfl
      intro i hi
      ring

/-- The emitted interval consists exactly of this round's selected endings. -/
theorem round_endings_eq_emitted_support {a : Multisegment} {r : Round}
    (h : round a = some r) : endings r.selected = r.emitted.support := by
  have hl : r.emitted.length = r.selectedList.length := by
    simp [Round.emitted, Interval.length, Round.selectedList]
  rw [endings, Round.selected, endings_of_consecutive r.selectedList r.first.ending
    (round_ending h)]
  unfold Interval.support
  rw [hl]
  apply Multiset.map_congr rfl
  intro i hi
  simp only [Round.emitted, Round.selectedList, List.length_cons]
  push_cast
  ring

/-- One round transfers its selected endings to the emitted interval. -/
theorem round_support_partition {a : Multisegment} {r : Round}
    (h : round a = some r) :
    r.emitted.support + support r.residual = support a := by
  rw [Round.residual, support_add, ← round_endings_eq_emitted_support h]
  calc
    _ = (support (shorten r.selected) + endings r.selected) +
        support r.untouched := by ac_rfl
    _ = support r.selected + support r.untouched := by
      rw [support_shorten_add_endings]
    _ = support a := by rw [← support_add, round_partition h]

/-- The actual total MW recursion preserves the full multiset of support points. -/
theorem supportPreservation : SupportPreservation := by
  intro a
  induction a using (measure (fun a : Multisegment => weight a)).wf.induction with
  | h a ih =>
    cases hr : round a with
    | none =>
      have ha : a = 0 := (round_none_iff a).1 hr
      subst a
      simp
    | some r =>
      rw [dual_of_round hr, support_cons, ih r.residual (round_weight_lt hr)]
      exact round_support_partition hr

end Langlands.MoeglinWaldspurger

import Langlands.Representation.Classification.MoeglinWaldspurgerStatements

/-!
# Badulescu property (P′) for the Moeglin–Waldspurger recursion

Each round emits an interval whose length is the number of selected
occurrences, and its residual has no more occurrences than its input.
Strong induction on `weight` proves the thickness bound.
-/

namespace Langlands.MoeglinWaldspurger

/-- Right truncation of each occurrence never increases the number of occurrences. -/
theorem card_shorten_le (a : Multisegment) : (shorten a).card ≤ a.card := by
  induction a using Multiset.induction_on with
  | empty => simp [shorten]
  | cons I a ih =>
    have hI : (Interval.dropLast I).card ≤ 1 := by
      unfold Interval.dropLast
      split_ifs <;> simp
    simp only [shorten, Multiset.cons_bind, Multiset.card_add, Multiset.card_cons] at *
    omega

/-- The emitted interval has one point per selected occurrence. -/
theorem Round.emitted_length (r : Round) : r.emitted.length = r.selected.card := by
  simp [Round.emitted, Interval.length, Round.selected, Round.selectedList]

theorem round_emitted_length_le {a : Multisegment} {r : Round} (h : round a = some r) :
    r.emitted.length ≤ a.card := by
  rw [r.emitted_length, ← round_partition h, Multiset.card_add]
  omega

theorem round_residual_card_le {a : Multisegment} {r : Round} (h : round a = some r) :
    r.residual.card ≤ a.card := by
  have hs := card_shorten_le r.selected
  rw [Round.residual, Multiset.card_add, ← round_partition h, Multiset.card_add]
  omega

/-- Badulescu (P′): every output interval of `dual a` has length at most `a.card`. -/
theorem thicknessBound : ThicknessBound := by
  intro a
  induction a using (measure weight).wf.induction with
  | h a ih =>
    cases hr : round a with
    | none =>
      rw [(round_none_iff a).1 hr, dual_zero]
      simp
    | some r =>
      rw [dual_of_round hr]
      intro J hJ
      rcases Multiset.mem_cons.1 hJ with rfl | hJ
      · exact round_emitted_length_le hr
      · exact (ih r.residual (round_weight_lt hr) J hJ).trans (round_residual_card_le hr)

end Langlands.MoeglinWaldspurger

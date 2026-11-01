import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Mathlib.Data.Multiset.Filter

/-! # Support obstructions for two adjacent cuspidal twists -/

noncomputable section

namespace Langlands.Classification.RepeatedCuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A multiset with `a` copies of `νρ` and `b` copies of `ρ`. -/
def pairSupport (ρ : T.CuspidalDatum.{uV, uF}) (a b : ℕ) :
    Multiset T.CuspidalDatum.{uV, uF} :=
  Multiset.replicate a (ρ.twist 1) + Multiset.replicate b ρ

/-- Consecutive integral twists of a positive-rank cuspidal datum differ. -/
theorem twist_one_ne_self (ρ : T.CuspidalDatum.{uV, uF}) : ρ.twist 1 ≠ ρ := by
  intro h
  have hz := (cuspidalIntegralTwistFreeness F T ρ 1).mp (by simpa using h)
  norm_num at hz

/-- The second integral twist cannot return to the original cuspidal datum. -/
theorem twist_two_ne_self (ρ : T.CuspidalDatum.{uV, uF}) : ρ.twist 2 ≠ ρ := by
  intro h
  have hz := (cuspidalIntegralTwistFreeness F T ρ 2).mp (by simpa using h)
  norm_num at hz

/-- If the shifted support lies on `ρ,νρ`, the unshifted support cannot contain `νρ`.
No restriction on the other unshifted entries is needed here. -/
theorem upper_not_mem_of_shift_le (ρ : T.CuspidalDatum.{uV, uF})
    (a b : ℕ) (s : Multiset T.CuspidalDatum.{uV, uF})
    (hshift : s.map (fun c => c.twist 1) ≤ pairSupport T ρ a b) :
    ρ.twist 1 ∉ s := by
  intro hmem
  have hm := Multiset.mem_of_le hshift (Multiset.mem_map.mpr ⟨ρ.twist 1, hmem, rfl⟩)
  have hnext : (ρ.twist 1).twist 1 ≠ ρ.twist 1 := twist_one_ne_self T (ρ.twist 1)
  have hbase : (ρ.twist 1).twist 1 ≠ ρ := by
    simpa only [PadicField.TopologicalData.CuspidalDatum.twist_twist,
      one_add_one_eq_two] using twist_two_ne_self T ρ
  simp only [pairSupport, Multiset.mem_add, Multiset.mem_replicate] at hm
  exact hm.elim (fun h => hnext h.2) (fun h => hbase h.2)

private theorem le_lower_of_upper_not_mem (ρ : T.CuspidalDatum.{uV, uF})
    (a b : ℕ) (s : Multiset T.CuspidalDatum.{uV, uF})
    (hs : s ≤ pairSupport T ρ a b) (hu : ρ.twist 1 ∉ s) :
    s ≤ Multiset.replicate b ρ := by
  induction a with
  | zero => simpa only [pairSupport, Multiset.replicate_zero, zero_add] using hs
  | succ a ih =>
    apply ih
    apply (Multiset.le_cons_of_notMem hu).mp
    simpa only [pairSupport, Multiset.replicate_succ, Multiset.cons_add] using hs

/-- A support and its positive shift can both lie in the adjacent pair only when
all entries are the lower datum, with multiplicity at most each endpoint's capacity. -/
theorem le_lower_min_of_support_and_shift_le (ρ : T.CuspidalDatum.{uV, uF})
    (a b : ℕ) (s : Multiset T.CuspidalDatum.{uV, uF})
    (hs : s ≤ pairSupport T ρ a b)
    (hshift : s.map (fun c => c.twist 1) ≤ pairSupport T ρ a b) :
    s ≤ Multiset.replicate (min a b) ρ := by
  classical
  have hlower := le_lower_of_upper_not_mem T ρ a b s hs
    (upper_not_mem_of_shift_le T ρ a b s hshift)
  obtain ⟨k, hkb, rfl⟩ := Multiset.le_replicate_iff.mp hlower
  have hka := Multiset.count_le_of_le (ρ.twist 1) hshift
  have hne : ρ ≠ ρ.twist 1 := (twist_one_ne_self T ρ).symm
  simp only [Multiset.map_replicate, pairSupport, Multiset.count_add,
    Multiset.count_replicate_self, Multiset.count_replicate, ite_eq_right hne, add_zero] at hka
  exact Multiset.replicate_mono ρ (le_min hka hkb)

/-- For the upper-repeat triple `{νρ,νρ,ρ}`, only zero or the singleton lower
support can satisfy both support inequalities. -/
theorem upper_repeat_support_eq (ρ : T.CuspidalDatum.{uV, uF})
    (s : Multiset T.CuspidalDatum.{uV, uF})
    (hs : s ≤ {ρ.twist 1, ρ.twist 1, ρ})
    (hshift : s.map (fun c => c.twist 1) ≤ {ρ.twist 1, ρ.twist 1, ρ}) :
    s = 0 ∨ s = {ρ} := by
  apply Multiset.le_singleton.mp
  have h := le_lower_min_of_support_and_shift_le T ρ 2 1 s
  simpa using
      h (by simpa [pairSupport, Multiset.replicate_succ, Multiset.cons_swap] using hs)
        (by simpa [pairSupport, Multiset.replicate_succ, Multiset.cons_swap] using hshift)

/-- The same obstruction for the lower-repeat triple `{νρ,ρ,ρ}`. -/
theorem lower_repeat_support_eq (ρ : T.CuspidalDatum.{uV, uF})
    (s : Multiset T.CuspidalDatum.{uV, uF})
    (hs : s ≤ {ρ.twist 1, ρ, ρ})
    (hshift : s.map (fun c => c.twist 1) ≤ {ρ.twist 1, ρ, ρ}) :
    s = 0 ∨ s = {ρ} := by
  apply Multiset.le_singleton.mp
  have h := le_lower_min_of_support_and_shift_le T ρ 1 2 s
  simpa using
      h (by simpa [pairSupport, Multiset.replicate_succ, Multiset.cons_swap] using hs)
        (by simpa [pairSupport, Multiset.replicate_succ, Multiset.cons_swap] using hshift)

end Langlands.Classification.RepeatedCuspidalSupport

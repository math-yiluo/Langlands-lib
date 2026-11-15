import Langlands.Representation.Classification.MoeglinWaldspurgerDerivativeStatements
import Langlands.Representation.Classification.MoeglinWaldspurgerInsertion
import Langlands.Representation.Classification.SpehNeighborMWBound
import Langlands.Representation.Classification.MoeglinWaldspurgerSupportProof
import Langlands.Representation.Classification.MoeglinWaldspurgerRealization

/-!
# Elementary combinatorics for the derivative comparison of the MW recursion

Facts about the bottom-up matching `unmatched`, its restriction to the occurrences ending at
`x` and `x - 1`, the first selected interval of a round, and endings of `dual`.
-/

namespace Langlands.MoeglinWaldspurger.Derivation

open Langlands.MoeglinWaldspurger

/-! ### The two relevant endings -/

/-- An occurrence ending at `x` or at `x - 1`. -/
def TwoEnd (x : ℤ) (I : Interval) : Prop := I.ending = x ∨ I.ending = x - 1

instance (x : ℤ) : DecidablePred (TwoEnd x) := fun I => by unfold TwoEnd; infer_instance

theorem unmatchedScan_filter (x : ℤ) :
    ∀ (l : List Interval) (pool : ℕ),
      unmatchedScan x (l.filter (fun I => decide (TwoEnd x I))) pool = unmatchedScan x l pool
  | [], _ => rfl
  | I :: l, pool => by
    by_cases h : TwoEnd x I
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [unmatchedScan]
      split_ifs <;> simp only [unmatchedScan_filter x l]
    · rw [List.filter_cons_of_neg (by simpa using h), unmatchedScan_filter x l pool]
      unfold TwoEnd at h
      simp only [unmatchedScan]
      simp only [show ¬ I.ending = x - 1 by omega, show ¬ I.ending = x by omega, ↓reduceIte]

theorem unmatchedScan_sublist (x : ℤ) :
    ∀ (l : List Interval) (pool : ℕ), (unmatchedScan x l pool).Sublist l
  | [], _ => List.Sublist.slnil
  | I :: l, pool => by
    simp only [unmatchedScan]
    split_ifs
    · exact (unmatchedScan_sublist x l _).cons I
    · exact (unmatchedScan_sublist x l _).cons_cons I
    · exact (unmatchedScan_sublist x l _).cons I
    · exact (unmatchedScan_sublist x l _).cons I

theorem mem_unmatchedScan_ending (x : ℤ) :
    ∀ (l : List Interval) (pool : ℕ) (I : Interval), I ∈ unmatchedScan x l pool → I.ending = x
  | [], _, _, h => by simp [unmatchedScan] at h
  | J :: l, pool, I, h => by
    simp only [unmatchedScan] at h
    split_ifs at h with h1 h2 h3
    · exact mem_unmatchedScan_ending x l _ I h
    · rcases List.mem_cons.mp h with rfl | h
      · exact h2
      · exact mem_unmatchedScan_ending x l _ I h
    · exact mem_unmatchedScan_ending x l _ I h
    · exact mem_unmatchedScan_ending x l _ I h

theorem sort_filter (s : Multiset Interval) (p : Interval → Prop) [DecidablePred p] :
    (s.filter p).sort ScanLE = (s.sort ScanLE).filter (fun I => decide (p I)) := by
  apply List.Perm.eq_of_pairwise' (r := ScanLE)
  · exact Multiset.pairwise_sort _ _
  · exact (Multiset.pairwise_sort s ScanLE).filter _
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, ← Multiset.filter_coe, Multiset.sort_eq]

theorem unmatched_filter (b : Multisegment) (x : ℤ) :
    unmatched (b.filter (TwoEnd x)) x = unmatched b x := by
  unfold unmatched
  rw [sort_filter, unmatchedScan_filter]

theorem unmatched_le (b : Multisegment) (x : ℤ) : unmatched b x ≤ b := by
  unfold unmatched
  conv_rhs => rw [← Multiset.sort_eq b ScanLE]
  exact Multiset.coe_le.mpr (unmatchedScan_sublist x _ 0).subperm

theorem mem_unmatched_ending {b : Multisegment} {x : ℤ} {I : Interval}
    (h : I ∈ unmatched b x) : I.ending = x :=
  mem_unmatchedScan_ending x _ 0 I h

theorem unmatched_le_filter (b : Multisegment) (x : ℤ) :
    unmatched b x ≤ b.filter (TwoEnd x) := by
  rw [← unmatched_filter]
  exact unmatched_le _ x

/-- Shortening the unmatched occurrences commutes with discarding the other endings. -/
theorem leftDerivative_eq_filter_add (b : Multisegment) (x : ℤ) :
    leftDerivative b x =
      b.filter (fun I => ¬ TwoEnd x I) + leftDerivative (b.filter (TwoEnd x)) x := by
  unfold leftDerivative
  rw [unmatched_filter]
  have hU := unmatched_le_filter b x
  have hb : b = b.filter (fun I => ¬ TwoEnd x I) + b.filter (TwoEnd x) := by
    rw [add_comm]; exact (Multiset.filter_add_not _ b).symm
  generalize unmatched b x = U at hU ⊢
  conv_lhs => rw [hb]
  rw [add_tsub_assoc_of_le hU, add_assoc]

theorem weight_leftDerivative_add_card (b : Multisegment) (x : ℤ) :
    weight (leftDerivative b x) + (unmatched b x).card = weight b := by
  unfold leftDerivative
  have h := weight_shorten_add_card (unmatched b x)
  have hb : b - unmatched b x + unmatched b x = b := tsub_add_cancel_of_le (unmatched_le b x)
  have hw := congrArg weight hb
  rw [weight_add] at hw
  rw [weight_add]
  omega

theorem weight_filter_le (b : Multisegment) (p : Interval → Prop) [DecidablePred p] :
    weight (b.filter p) ≤ weight b := by
  have := congrArg weight (Multiset.filter_add_not p b)
  rw [weight_add] at this
  omega

theorem weight_filter_lt (b : Multisegment) (p : Interval → Prop) [DecidablePred p]
    {I : Interval} (hI : I ∈ b) (hp : ¬ p I) : weight (b.filter p) < weight b := by
  have h := congrArg weight (Multiset.filter_add_not p b)
  rw [weight_add] at h
  have hmem : I ∈ b.filter (fun J => ¬ p J) := Multiset.mem_filter.mpr ⟨hI, hp⟩
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem
  have : 0 < weight (b.filter fun J => ¬ p J) := by
    rw [ht, weight_cons]
    exact Nat.add_pos_left I.length_pos _
  omega

/-- Shortening keeps the endings `x` and `x - 1` among the endings `x` and `x - 1`. -/
theorem twoEnd_of_mem_leftDerivative {J : Multisegment} {x : ℤ}
    (hJ : ∀ I ∈ J, TwoEnd x I) : ∀ I ∈ leftDerivative J x, TwoEnd x I := by
  intro I hI
  unfold leftDerivative at hI
  rcases Multiset.mem_add.mp hI with h | h
  · exact hJ I (Multiset.mem_of_le (tsub_le_self) h)
  · obtain ⟨K, hK, hIK⟩ := Multiset.mem_bind.mp h
    have hKe := mem_unmatched_ending hK
    unfold Interval.dropLast at hIK
    split_ifs at hIK with hlt
    · rw [Multiset.mem_singleton] at hIK
      subst hIK
      right
      simp [hKe]
    · simp at hIK

/-! ### Endings of the MW output -/

theorem mem_support_iff {a : Multisegment} {z : ℤ} :
    z ∈ support a ↔ ∃ I ∈ a, z ∈ I.support := Multiset.mem_bind

theorem mem_interval_support {I : Interval} {z : ℤ} :
    z ∈ I.support ↔ I.beginning ≤ z ∧ z ≤ I.ending := by
  unfold Interval.support Interval.length
  simp only [Multiset.mem_map, Multiset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := Int.toNat_of_nonneg (sub_nonneg.mpr I.nonempty)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(z - I.beginning).toNat, ?_, ?_⟩ <;> omega

theorem ending_mem_support (I : Interval) : I.ending ∈ I.support :=
  mem_interval_support.mpr ⟨I.nonempty, le_rfl⟩

/-- If every input interval ends at most at `e`, so does every output interval. -/
theorem dual_ending_le {a : Multisegment} {e : ℤ} (h : ∀ I ∈ a, I.ending ≤ e) :
    ∀ J ∈ dual a, J.ending ≤ e := by
  intro J hJ
  have hz : J.ending ∈ support (dual a) :=
    mem_support_iff.mpr ⟨J, hJ, ending_mem_support J⟩
  rw [supportPreservation a] at hz
  obtain ⟨I, hI, hzI⟩ := mem_support_iff.mp hz
  exact (mem_interval_support.mp hzI).2.trans (h I hI)

theorem weight_dual (a : Multisegment) : weight (dual a) = weight a := by
  rw [← support_card, ← support_card, supportPreservation a]

end Langlands.MoeglinWaldspurger.Derivation

namespace Langlands.MoeglinWaldspurger.Derivation

open Langlands.MoeglinWaldspurger

/-! ### Rounds -/

theorem round_first_maximal {a : Multisegment} {r : Round}
    (h : round a = some r) {I : Interval} (hI : I ∈ a) : I ≤ r.first := by
  have hs := Multiset.pairwise_sort a (fun I J : Interval => J ≤ I)
  have hm := (Multiset.mem_sort (fun I J : Interval => J ≤ I)).mpr hI
  unfold round at h
  cases hl : a.sort (fun I J : Interval => J ≤ I) with
  | nil => simp [hl] at h
  | cons J l =>
    simp only [hl, Option.some.injEq] at h
    subst r
    rw [hl] at hs hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_rfl
    · exact (List.pairwise_cons.mp hs).1 _ hm

theorem round_chain_eq {a : Multisegment} {r : Round} (h : round a = some r) :
    chain (a.erase r.first) (r.first.ending - 1) r.first.beginning =
      (r.tail, r.untouched) := by
  unfold round at h
  cases hl : a.sort (fun I J : Interval => J ≤ I) with
  | nil => simp [hl] at h
  | cons I l =>
    simp only [hl, Option.some.injEq] at h
    subst r
    have ha : I ::ₘ (l : Multisegment) = a := by
      simpa [hl] using Multiset.sort_eq a (fun I J : Interval => J ≤ I)
    simp [← ha]

theorem shorten_ending_le {s : Multisegment} {e : ℤ} (hs : ∀ I ∈ s, I.ending ≤ e) :
    ∀ J ∈ shorten s, J.ending ≤ e - 1 := by
  intro J hJ
  obtain ⟨K, hK, hJK⟩ := Multiset.mem_bind.mp hJ
  unfold Interval.dropLast at hJK
  split_ifs at hJK
  · rw [Multiset.mem_singleton] at hJK
    subst hJK
    have := hs K hK
    simp only
    omega
  · simp at hJK

theorem round_residual_ending_le {a : Multisegment} {r : Round} (h : round a = some r) :
    ∀ I ∈ r.residual, I.ending ≤ r.first.ending := by
  have hp := round_partition h
  intro I hI
  rcases Multiset.mem_add.mp hI with hu | hs
  · exact Langlands.MoeglinWaldspurger.round_ending_le_first h (by rw [← hp]; exact Multiset.mem_add.mpr (Or.inr hu))
  · have := shorten_ending_le (s := r.selected) (e := r.first.ending)
      (fun J hJ => Langlands.MoeglinWaldspurger.round_ending_le_first h (by rw [← hp]; exact Multiset.mem_add.mpr (Or.inl hJ))) I hs
    omega

theorem leftDerivative_ending_le {b : Multisegment} {e : ℤ} (hb : ∀ I ∈ b, I.ending ≤ e)
    (x : ℤ) : ∀ I ∈ leftDerivative b x, I.ending ≤ e := by
  intro I hI
  unfold leftDerivative at hI
  rcases Multiset.mem_add.mp hI with h | h
  · exact hb I (Multiset.mem_of_le tsub_le_self h)
  · have := shorten_ending_le (s := unmatched b x) (e := e)
      (fun J hJ => hb J (Multiset.mem_of_le (unmatched_le b x) hJ)) I h
    omega

theorem chain_eq_nil_iff (a : Multisegment) (e b : ℤ) :
    (chain a e b).1 = [] ↔ pick a e b = none := by
  rw [chain]
  split
  · rename_i hp; simp [hp]
  · rename_i I hp; simp [hp]

theorem chain_of_pick_none {a : Multisegment} {e b : ℤ} (hp : pick a e b = none) :
    chain a e b = ([], a) := by
  rw [chain]
  split
  · rfl
  · rename_i I hI; rw [hp] at hI; cases hI

end Langlands.MoeglinWaldspurger.Derivation

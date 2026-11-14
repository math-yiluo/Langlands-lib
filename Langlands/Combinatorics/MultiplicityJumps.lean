import Mathlib

/-!
# Jumps of an antitone sequence with prescribed multiplicities

Let `a : Fin n → ℤ` be nonnegative and antitone, and let `b : Fin r → ℤ` be positive and
injective. Suppose that every positive value `v` is taken by `a` exactly `deg` times as
often as by `b`. Then, for `i + 1 < n`, the values `a i` and `a (i + 1)` differ exactly when
`i + 1 = j * deg` for some `0 < j ≤ r`. We also count signed solutions of `s * f i = v`.
-/

namespace Langlands.Combinatorics.MultiplicityJumps

open Finset

/-- For `v > 0`, the pairs `(i, s)` with `s = ±1` and `s * f i = v` correspond to the
indices `i` with `|f i| = v`. -/
theorem natCard_signed_eq {ι : Type*} [Fintype ι] (f : ι → ℤ) {v : ℤ} (hv : 0 < v) :
    Nat.card {p : ι × ℤˣ // (p.2 : ℤ) * f p.1 = v} = #{i | |f i| = v} := by
  classical
  have key : Nat.card {p : ι × ℤˣ // (p.2 : ℤ) * f p.1 = v} =
      Nat.card {i : ι // |f i| = v} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun p => ⟨p.1.1, by
        have h := congrArg (fun x : ℤ => |x|) p.2
        have hu : |((p.1.2 : ℤˣ) : ℤ)| = 1 := by
          rcases Int.units_eq_one_or p.1.2 with hs | hs <;> simp [hs]
        simp only [abs_mul, hu, one_mul] at h
        rw [h, abs_of_pos hv]⟩) ⟨?_, ?_⟩)
    · rintro ⟨⟨i, s⟩, hs⟩ ⟨⟨i', s'⟩, hs'⟩ h
      simp only [Subtype.mk.injEq] at h
      subst h
      have hfi : f i ≠ 0 := by
        rintro h0
        rw [h0, mul_zero] at hs
        exact hv.ne hs
      have : (s : ℤ) = s' := mul_right_cancel₀ hfi (hs.trans hs'.symm)
      have hss : s = s' := Units.ext this
      subst hss
      rfl
    · rintro ⟨i, hi⟩
      rcases abs_eq hv.le |>.1 hi with h | h
      · exact ⟨⟨(i, 1), by simp [h]⟩, rfl⟩
      · exact ⟨⟨(i, -1), by simp [h]⟩, rfl⟩
  rw [key, Nat.card_eq_fintype_card, Fintype.card_subtype]

variable {n r : ℕ}

/-- A downward closed finite set of `Fin n` is the initial segment of its cardinality. -/
theorem mem_iff_lt_card {s : Finset (Fin n)} (hs : ∀ i j, i ≤ j → j ∈ s → i ∈ s)
    (i : Fin n) : i ∈ s ↔ (i : ℕ) < #s := by
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ s := fun j hj => hs j i (Finset.mem_Iic.1 hj) hi
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hi
    have hsub : s ⊆ Finset.Iio i := fun j hj =>
      Finset.mem_Iio.2 (lt_of_not_ge fun hij => hi (hs i j hij hj))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- The multiplicity relation passes from values to upper level sets. -/
theorem card_le_eq (deg : ℕ) (a : Fin n → ℤ) (b : Fin r → ℤ)
    (hcount : ∀ v : ℤ, 0 < v → #{i | a i = v} = deg * #{k | b k = v})
    {v : ℤ} (hv : 0 < v) :
    #{i | v ≤ a i} = deg * #{k | v ≤ b k} := by
  classical
  set W : Finset ℤ := (univ.image a ∪ univ.image b).filter (v ≤ ·) with hW
  have hA : #{i | v ≤ a i} = ∑ w ∈ W, #{i | a i = w} := by
    rw [card_eq_sum_card_fiberwise (f := a) (t := W)]
    · refine sum_congr rfl fun w hw => ?_
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [h]
        exact (mem_filter.1 hw).2
    · intro i hi
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi
      simp [hW, hi]
  have hB : #{k | v ≤ b k} = ∑ w ∈ W, #{k | b k = w} := by
    rw [card_eq_sum_card_fiberwise (f := b) (t := W)]
    · refine sum_congr rfl fun w hw => ?_
      congr 1
      ext k
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rw [h]
        exact (mem_filter.1 hw).2
    · intro k hk
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
      simp [hW, hk]
  rw [hA, hB, mul_sum]
  refine sum_congr rfl fun w hw => hcount w ?_
  exact lt_of_lt_of_le hv (mem_filter.1 hw).2

/-- Upper level sets of an injective function shrink by at most one per step. -/
theorem card_le_le_succ (b : Fin r → ℤ) (hb : Function.Injective b) (v : ℤ) :
    #{k | v ≤ b k} ≤ #{k | v + 1 ≤ b k} + 1 := by
  have hsub : ({k | v ≤ b k} : Finset (Fin r)) ⊆
      ({k | v + 1 ≤ b k} : Finset (Fin r)) ∪ ({k | b k = v} : Finset (Fin r)) := by
    intro k hk
    simp only [mem_filter, mem_univ, true_and, mem_union] at hk ⊢
    omega
  have hone : #({k | b k = v} : Finset (Fin r)) ≤ 1 := by
    refine Finset.card_le_one.2 fun x hx y hy => hb ?_
    simp only [mem_filter, mem_univ, true_and] at hx hy
    rw [hx, hy]
  calc #{k | v ≤ b k} ≤ #(({k | v + 1 ≤ b k} : Finset (Fin r)) ∪
        ({k | b k = v} : Finset (Fin r))) := Finset.card_le_card hsub
    _ ≤ #{k | v + 1 ≤ b k} + #({k | b k = v} : Finset (Fin r)) := Finset.card_union_le _ _
    _ ≤ _ := by omega

/-- Every integer `0 < j ≤ r` is the size of an upper level set `{k | v ≤ b k}` with
`v > 0`, when `b` is positive and injective. -/
theorem exists_card_le_eq (b : Fin r → ℤ) (hb0 : ∀ k, 0 < b k)
    (hb : Function.Injective b) {j : ℕ} (hj0 : 0 < j) (hjr : j ≤ r) :
    ∃ v : ℤ, 0 < v ∧ #{k | v ≤ b k} = j := by
  classical
  have hex : ∃ t : ℕ, #{k | (1 : ℤ) + t ≤ b k} < j := by
    refine ⟨(∑ k, b k).toNat, ?_⟩
    have : ({k | (1 : ℤ) + ((∑ k, b k).toNat : ℕ) ≤ b k} : Finset (Fin r)) = ∅ := by
      refine Finset.filter_false_of_mem fun k _ => ?_
      have h1 : b k ≤ ∑ k, b k :=
        Finset.single_le_sum (f := b) (fun l _ => (hb0 l).le) (mem_univ k)
      have h2 : (∑ k, b k) ≤ (((∑ k, b k).toNat : ℕ) : ℤ) := Int.self_le_toNat _
      omega
    rw [this, card_empty]
    exact hj0
  set t := Nat.find hex with ht
  have hspec : #{k | (1 : ℤ) + t ≤ b k} < j := Nat.find_spec hex
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at hspec
    have : ({k | (1 : ℤ) + ((0 : ℕ) : ℤ) ≤ b k} : Finset (Fin r)) = univ := by
      refine Finset.filter_true_of_mem fun k _ => ?_
      have := hb0 k
      push_cast
      omega
    rw [this, card_univ, Fintype.card_fin] at hspec
    omega
  have hmin : ¬ #{k | (1 : ℤ) + ((t - 1 : ℕ) : ℤ) ≤ b k} < j :=
    Nat.find_min hex (by omega)
  have hcast : (1 : ℤ) + ((t - 1 : ℕ) : ℤ) + 1 = 1 + (t : ℤ) := by
    have : 1 ≤ t := Nat.one_le_iff_ne_zero.2 ht0
    push_cast [this]
    ring
  have hstep := card_le_le_succ b hb ((1 : ℤ) + ((t - 1 : ℕ) : ℤ))
  rw [hcast] at hstep
  refine ⟨1 + ((t - 1 : ℕ) : ℤ), by positivity, ?_⟩
  omega

/-- **Jump lemma.** Let `a : Fin n → ℤ` be nonnegative and antitone and `b : Fin r → ℤ`
positive and injective, with `#{i | a i = v} = deg * #{k | b k = v}` for every `v > 0`.
Then for `i + 1 < n`, `a i ≠ a (i + 1)` exactly when `i + 1 = j * deg` for
some `0 < j ≤ r`. -/
theorem ne_succ_iff (deg : ℕ) (a : Fin n → ℤ) (b : Fin r → ℤ)
    (ha0 : ∀ i, 0 ≤ a i) (hanti : Antitone a)
    (hb0 : ∀ k, 0 < b k) (hb : Function.Injective b)
    (hcount : ∀ v : ℤ, 0 < v → #{i | a i = v} = deg * #{k | b k = v})
    (i : ℕ) (hi : i + 1 < n) :
    a ⟨i, by omega⟩ ≠ a ⟨i + 1, hi⟩ ↔ ∃ j : ℕ, 0 < j ∧ j ≤ r ∧ i + 1 = j * deg := by
  classical
  have hdown : ∀ v : ℤ, ∀ x y : Fin n, x ≤ y →
      y ∈ ({l | v ≤ a l} : Finset (Fin n)) → x ∈ ({l | v ≤ a l} : Finset (Fin n)) := by
    intro v x y hxy hy
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact hy.trans (hanti hxy)
  have hle : a ⟨i + 1, hi⟩ ≤ a ⟨i, by omega⟩ := hanti (Fin.mk_le_mk.2 (Nat.le_succ i))
  constructor
  · intro hne
    have hlt : a ⟨i + 1, hi⟩ < a ⟨i, by omega⟩ := lt_of_le_of_ne hle (Ne.symm hne)
    set v := a ⟨i, by omega⟩ with hv
    have hvpos : 0 < v := lt_of_le_of_lt (ha0 _) hlt
    have hmem := mem_iff_lt_card (hdown v) ⟨i, by omega⟩
    have hmem' := mem_iff_lt_card (hdown v) ⟨i + 1, hi⟩
    simp only [mem_filter, mem_univ, true_and] at hmem hmem'
    have h1 : i < #{l | v ≤ a l} := hmem.1 le_rfl
    have h2 : ¬ i + 1 < #{l | v ≤ a l} := fun h => (not_le.2 hlt) (hmem'.2 h)
    have hA : #{l | v ≤ a l} = i + 1 := by omega
    rw [card_le_eq deg a b hcount hvpos] at hA
    refine ⟨#{k | v ≤ b k}, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos #{k | v ≤ b k} with h | h
      · rw [h, mul_zero] at hA
        omega
      · exact h
    · calc #{k | v ≤ b k} ≤ #(univ : Finset (Fin r)) := Finset.card_le_card (filter_subset _ _)
        _ = r := by rw [card_univ, Fintype.card_fin]
    · rw [← hA, mul_comm]
  · rintro ⟨j, hj0, hjr, hij⟩
    obtain ⟨v, hvpos, hvj⟩ := exists_card_le_eq b hb0 hb hj0 hjr
    have hA : #{l | v ≤ a l} = i + 1 := by
      rw [card_le_eq deg a b hcount hvpos, hvj, hij, mul_comm]
    have hmem := mem_iff_lt_card (hdown v) ⟨i, by omega⟩
    have hmem' := mem_iff_lt_card (hdown v) ⟨i + 1, hi⟩
    simp only [mem_filter, mem_univ, true_and, hA] at hmem hmem'
    have h1 : v ≤ a ⟨i, by omega⟩ := hmem.2 (Nat.lt_succ_self i)
    have h2 : ¬ v ≤ a ⟨i + 1, hi⟩ := fun h => (lt_irrefl _) (hmem'.1 h)
    intro heq
    rw [heq] at h1
    exact h2 h1

/-- **Signed version for a type-`D` chain.** Let `c : Fin n → ℤ` satisfy
`c (j + 1) ≤ c j` for `j + 1 < n` and `0 ≤ c (n - 2) + c (n - 1)`, and let `b : Fin r → ℤ`
have nonzero values with `b k ≠ ± b l` for `k ≠ l`. Suppose that for every `v > 0` the
number of pairs `(i, s)`, `s = ±1`, with `s * c i = v` is `deg` times the number of pairs
`(k, s)` with `s * b k = v`. Then for `i + 2 < n`, `c i ≠ c (i + 1)` exactly when
`i + 1 = j * deg` for some `0 < j ≤ r`. -/
theorem chain_ne_succ_iff (deg : ℕ) (hn : 2 ≤ n) (c : Fin n → ℤ) (b : Fin r → ℤ)
    (hstep : ∀ (j : ℕ) (h : j + 1 < n), c ⟨j + 1, h⟩ ≤ c ⟨j, by omega⟩)
    (hfork : 0 ≤ c ⟨n - 2, by omega⟩ + c ⟨n - 1, by omega⟩)
    (hb0 : ∀ k, b k ≠ 0) (hb : ∀ k l, k ≠ l → b k ≠ b l ∧ b k ≠ -b l)
    (hcount : ∀ v : ℤ, 0 < v →
      Nat.card {p : Fin n × ℤˣ // (p.2 : ℤ) * c p.1 = v} =
        deg * Nat.card {p : Fin r × ℤˣ // (p.2 : ℤ) * b p.1 = v})
    (i : ℕ) (hi : i + 2 < n) :
    c ⟨i, by omega⟩ ≠ c ⟨i + 1, by omega⟩ ↔ ∃ j : ℕ, 0 < j ∧ j ≤ r ∧ i + 1 = j * deg := by
  classical
  have hanti_c : ∀ i j : Fin n, i ≤ j → c j ≤ c i := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.mk_le_mk] at hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (hstep j hj).trans (ih (by omega))
  have hlast : c ⟨n - 1, by omega⟩ ≤ c ⟨n - 2, by omega⟩ := by
    have h := hstep (n - 2) (by omega)
    have e1 : (⟨n - 2 + 1, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
    rwa [e1] at h
  have hpen : 0 ≤ c ⟨n - 2, by omega⟩ := by linarith
  have hnonneg : ∀ j : Fin n, (j : ℕ) + 1 < n → 0 ≤ c j := fun j hj =>
    hpen.trans (hanti_c j ⟨n - 2, by omega⟩ (Fin.mk_le_mk.2 (by omega)))
  have habs_last : |c ⟨n - 1, by omega⟩| ≤ c ⟨n - 2, by omega⟩ :=
    abs_le.2 ⟨by linarith, hlast⟩
  have hanti : Antitone fun j : Fin n => |c j| := by
    intro i j hij
    by_cases hj : (j : ℕ) + 1 < n
    · simp only
      rw [abs_of_nonneg (hnonneg j hj),
        abs_of_nonneg (hnonneg i (lt_of_le_of_lt (Nat.succ_le_succ (Fin.le_def.1 hij)) hj))]
      exact hanti_c i j hij
    · have hjeq : j = ⟨n - 1, by omega⟩ := Fin.ext (by simp; omega)
      by_cases hij' : i = j
      · rw [hij']
      · have hi' : (i : ℕ) + 1 < n := by
          have := Fin.le_def.1 hij
          have : (i : ℕ) ≠ j := fun h => hij' (Fin.ext h)
          omega
        simp only
        rw [hjeq, abs_of_nonneg (hnonneg i hi')]
        exact habs_last.trans (hanti_c i ⟨n - 2, by omega⟩ (Fin.mk_le_mk.2 (by omega)))
  have hbabs_inj : Function.Injective fun k => |b k| := by
    intro k l hkl
    by_contra hne
    rcases abs_eq_abs.1 hkl with h | h
    · exact (hb k l hne).1 h
    · exact (hb k l hne).2 h
  have hcount' : ∀ v : ℤ, 0 < v →
      #{j | |c j| = v} = deg * #{k | |b k| = v} := by
    intro v hv
    rw [← natCard_signed_eq c hv, ← natCard_signed_eq b hv]
    exact hcount v hv
  have key := ne_succ_iff deg (fun j => |c j|) (fun k => |b k|) (fun j => abs_nonneg _)
    hanti (fun k => abs_pos.2 (hb0 k)) hbabs_inj hcount' i (by omega)
  rw [← key, abs_of_nonneg (hnonneg _ (by simp; omega)),
    abs_of_nonneg (hnonneg _ (by simp; omega))]

end Langlands.Combinatorics.MultiplicityJumps

import Langlands.Correspondence.HenniartPolarPartCountingIdentityProof

/-!
# Truncated uniqueness of the polar-part identity

This proves the converse of route-note Lemma 3.3 at `f = 1` with the
slope truncation used in Proposition 5.12(b).
-/

namespace Langlands.Henniart

open Numerical

private theorem sum_polarTwistCount {q n : ℕ} (hq : IsPrimePow q) (hn : 1 ≤ n) (j : ℕ) :
    (∑ d ∈ n.divisors, ∑ k ∈ (Finset.range (j + 1)).filter (fun k => n * k ≤ d * j),
      (polarTwistCount q d k : ℕ∞)) = (((q - 1) * q ^ j : ℕ) : ℕ∞) := by
  have hcount := polarPartCountingIdentity q hq n 1 j hn le_rfl (one_dvd n)
  simp only [Nat.div_one, Nat.cast_one, one_mul, one_dvd, true_and, Nat.divisors_one,
    Finset.sum_singleton, ArithmeticFunction.moebius_apply_one, pow_one] at hcount
  have hqSub : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    simpa only [Nat.cast_one] using Int.natCast_sub hq.one_lt.le
  rw [← hqSub] at hcount
  have hnat :
      (∑ m ∈ n.divisors, ∑ k ∈ (Finset.range (j + 1)).filter (fun k => m * k ≤ j),
        polarTwistCount q (n / m) k) = (q - 1) * q ^ j := by
    unfold polarTwistCount
    exact_mod_cast hcount
  have hsum :
      (∑ d ∈ n.divisors, ∑ k ∈ (Finset.range (j + 1)).filter (fun k => n * k ≤ d * j),
        polarTwistCount q d k) = (q - 1) * q ^ j := by
    rw [← hnat, ← Nat.sum_divisorsAntidiagonal (fun d _ =>
      ∑ k ∈ (Finset.range (j + 1)).filter (fun k => n * k ≤ d * j), polarTwistCount q d k),
      ← Nat.sum_divisorsAntidiagonal' (fun d m =>
        ∑ k ∈ (Finset.range (j + 1)).filter (fun k => m * k ≤ j), polarTwistCount q d k)]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hpos := Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
    have hfilter (k : ℕ) : n * k ≤ p.1 * j ↔ p.2 * k ≤ j := by
      rw [← hmul, Nat.mul_assoc, mul_le_mul_iff_right₀ hpos]
    simp only [hfilter]
  exact_mod_cast hsum

/-- The counting identities below slope `e` determine all polar twist counts below `e`. -/
theorem polarPartTruncatedUniqueness : PolarPartTruncatedUniquenessStatement := by
  intro q hq e T hT n
  let twist (d k : ℕ) : ℕ∞ := polarTwistCount q d k
  induction n using Nat.strong_induction_on with
  | h n ihRank =>
    intro s hn hs
    induction s using Nat.strong_induction_on with
    | h s ihSwan =>
      let indices (d : ℕ) := (Finset.range (s + 1)).filter (fun k => n * k ≤ d * s)
      let remainder (A : ℕ → ℕ → ℕ∞) :=
        (∑ d ∈ n.divisors.erase n, ∑ k ∈ indices d, A d k) +
          ∑ k ∈ Finset.range s, A n k
      have hnDiv := Nat.mem_divisors_self n (Nat.ne_of_gt hn)
      have hIndices : indices n = Finset.range (s + 1) := by
        ext k
        simp only [indices, Finset.mem_filter, Finset.mem_range]
        exact ⟨And.left, fun hk => ⟨hk, Nat.mul_le_mul_left n (Nat.le_of_lt_succ hk)⟩⟩
      have hsplit (A : ℕ → ℕ → ℕ∞) :
          (∑ d ∈ n.divisors, ∑ k ∈ indices d, A d k) = remainder A + A n s := by
        rw [← Finset.sum_erase_add _ _ hnDiv, hIndices, Finset.sum_range_succ]
        simp only [remainder, add_assoc]
      have hremain : remainder T = remainder twist := by
        unfold remainder
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro d hd
          obtain ⟨hdn, hdDiv⟩ := Finset.mem_erase.mp hd
          have hdpos := Nat.pos_of_mem_divisors hdDiv
          have hdlt := lt_of_le_of_ne (Nat.divisor_le hdDiv) hdn
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hkd : k < d * e := by
            apply (Nat.mul_lt_mul_left hn).mp
            calc
              n * k ≤ d * s := (Finset.mem_filter.mp hk).2
              _ < d * (n * e) := Nat.mul_lt_mul_of_pos_left hs hdpos
              _ = n * (d * e) := by ac_rfl
          exact ihRank d hdlt k hdpos hkd
        · refine Finset.sum_congr rfl ?_
          intro k hk
          have hks := Finset.mem_range.mp hk
          exact ihSwan k hks (hks.trans hs)
      have htotal := (hsplit T).symm.trans (hT n s hn hs)
      have htwist := (hsplit twist).symm.trans (sum_polarTwistCount hq hn s)
      rw [hremain] at htotal
      have hfinite : remainder twist ≠ ⊤ :=
        ne_top_of_le_ne_top (ENat.natCast_ne_top _) (le_self_add.trans_eq htwist)
      exact WithTop.add_left_cancel hfinite (htotal.trans htwist.symm)

end Langlands.Henniart

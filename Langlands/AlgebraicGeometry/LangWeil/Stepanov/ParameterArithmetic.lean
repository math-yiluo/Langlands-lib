import Mathlib

/-!
# Parameter arithmetic for Stepanov's method

The elementary inequalities between the parameters `n, m, M, q, d, N₁, N₂` that
the Stepanov norm-polynomial construction (Schmidt, *Zur Methode von Stepanov*, 1973)
needs. There are two dimension counts for the linear systems, the bound needed by
Frobenius independence (Hilfssatz 3), and two final degree bounds.
-/

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

namespace ParamArith

/-- Closed form of an arithmetic sum: `2 · ∑_{l ≤ s} (α + β l) = 2 α (s + 1) + β (s + 1) s`. -/
lemma two_mul_sum_affine (α β s : ℕ) :
    2 * ∑ l ∈ Finset.range (s + 1), (α + β * l) = 2 * α * (s + 1) + β * ((s + 1) * s) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  have h := Finset.sum_range_id_mul_two (s + 1)
  rw [Nat.add_sub_cancel] at h
  rw [← h]
  ring

end ParamArith

open ParamArith in
/-- The parameter inequalities of the Stepanov method. Let `2 ≤ n ≤ m`, `0 < M`, and
`M² (n² + 1) + (M + m) n² < q`. Put `d = ⌊q/n⌋ - m n`, `N₁ = ⌊(M + m)/n⌋`, and
`N₂ = ⌊(n - 1)(M + m)/n⌋`. Then the five inequalities below hold. -/
theorem stepanovParameterArithmetic :
    ∀ (n m M q : ℕ), 2 ≤ n → n ≤ m → 0 < M →
    M ^ 2 * (n ^ 2 + 1) + (M + m) * n ^ 2 < q →
    let d := q / n - m * n
    let N₁ := (M + m) / n
    let N₂ := (n - 1) * (M + m) / n
    n * d + m * (n - 1) ^ 2 < q ∧
    ∑ l ∈ Finset.range M,
        (n * (d + l * (2 * m - 1) + N₁ + 1) + m * ((n - 1) * (2 * l + 2) + 1 - n))
      < n * n * (N₁ + 1) * (d + 1) ∧
    (n - 1) * ∑ l ∈ Finset.range M,
        (n * (d + l * (2 * m - 1) + N₂ + m + 1) + m * ((n - 1) * (2 * l + 2) + 1 - n))
      < n * n * (N₂ + 1) * (d + 1) ∧
    m * ((n - 1) * (q + 1)) + n * (d + q * N₁) < q * (M + (2 * m * (n - 1) + 1)) ∧
    m * ((n - 1) * (q + 1)) + n * (d + q * N₂) < q * ((n - 1) * M + (2 * m * (n - 1) + 1)) := by
  intro n m M q hn hnm hM hH d N₁ N₂
  have hd_def : d = q / n - m * n := rfl
  have hN₁_def : N₁ = (M + m) / n := rfl
  have hN₂_def : N₂ = (n - 1) * (M + m) / n := rfl
  clear_value d N₁ N₂
  have hn0 : 0 < n := by omega
  -- Facts about `d`: `n d + m n² ≤ q < n d + n + m n²`.
  have hq1 : m * n ^ 2 < q := by
    linarith [Nat.zero_le (M ^ 2 * (n ^ 2 + 1)), Nat.zero_le (M * n ^ 2)]
  have hqn : m * n ≤ q / n := (Nat.le_div_iff_mul_le hn0).2 (by nlinarith [hq1])
  have hd_eq : d + m * n = q / n := by omega
  have hnq : n * (q / n) = n * d + m * n ^ 2 := by rw [← hd_eq]; ring
  have hdm := Nat.div_add_mod q n
  have hmod := Nat.mod_lt q hn0
  have hd1 : n * d + m * n ^ 2 ≤ q := by omega
  have hd2 : q + 1 ≤ n * d + n + m * n ^ 2 := by omega
  -- Facts about `N₁` and `N₂`.
  have hN1a : n * N₁ ≤ M + m := by rw [hN₁_def]; exact Nat.mul_div_le (M + m) n
  have hN1b : M + m < n * (N₁ + 1) := by rw [hN₁_def]; exact Nat.lt_mul_div_succ (M + m) hn0
  have hN2a : n * N₂ ≤ (n - 1) * (M + m) := by
    rw [hN₂_def]; exact Nat.mul_div_le ((n - 1) * (M + m)) n
  have hN2b : (n - 1) * (M + m) < n * (N₂ + 1) := by
    rw [hN₂_def]; exact Nat.lt_mul_div_succ ((n - 1) * (M + m)) hn0
  clear hd_def hN₁_def hN₂_def hd_eq hnq hdm hmod hqn
  -- Substitute `n = a + 2`, `m = c + 1`, `M = s + 1`.
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 2 := ⟨n - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, m = c + 1 := ⟨m - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, M = s + 1 := ⟨M - 1, by omega⟩
  have ha1 : a + 2 - 1 = a + 1 := by omega
  rw [ha1] at hN2a hN2b
  -- The common `l`-coefficient of the summands.
  have key : ∀ l : ℕ, (c + 1) * ((a + 2 - 1) * (2 * l + 2) + 1 - (a + 2)) =
      (c + 1) * (a + 1) + 2 * (c + 1) * (a + 1) * l := by
    intro l
    have h : (a + 2 - 1) * (2 * l + 2) = (a + 1) * (2 * l + 1) + (a + 1) := by
      rw [ha1]; ring
    have h' : (a + 2 - 1) * (2 * l + 2) + 1 - (a + 2) = (a + 1) * (2 * l + 1) := by omega
    rw [h']; ring
  have hc2 : 2 * (c + 1) - 1 = 2 * c + 1 := by omega
  -- `A = n (d + 1)` is large: `X + 2 ≤ A`.
  have P3 : (s + 1) ^ 2 * ((a + 2) ^ 2 + 1) + (s + 1) * (a + 2) ^ 2 + 2 ≤ (a + 2) * (d + 1) := by
    linarith [hd2, hH]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Frobenius-independence bound.
    rw [ha1]
    linarith [hd1, Nat.zero_le (c * a)]
  · -- First dimension count.
    have hS : ∑ l ∈ Finset.range (s + 1),
        ((a + 2) * (d + l * (2 * (c + 1) - 1) + N₁ + 1) +
          (c + 1) * ((a + 2 - 1) * (2 * l + 2) + 1 - (a + 2))) =
        ∑ l ∈ Finset.range (s + 1),
          (((a + 2) * (d + N₁ + 1) + (c + 1) * (a + 1)) +
            ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * l) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [key l, hc2]; ring
    rw [hS]
    have h2 := two_mul_sum_affine ((a + 2) * (d + N₁ + 1) + (c + 1) * (a + 1))
      ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) s
    have P1 : (a + 2) * (d + 1) * (s + 1 + (c + 1) + 1) ≤ (a + 2) * (d + 1) * ((a + 2) * (N₁ + 1)) :=
      Nat.mul_le_mul_left _ hN1b
    have P2 : (s + 1) * ((a + 2) * N₁) ≤ (s + 1) * (s + 1 + (c + 1)) :=
      Nat.mul_le_mul_left _ hN1a
    have P4 : (c + 2) * ((s + 1) ^ 2 * ((a + 2) ^ 2 + 1) + (s + 1) * (a + 2) ^ 2 + 2) ≤
        (c + 2) * ((a + 2) * (d + 1)) :=
      Nat.mul_le_mul_left _ P3
    have Q1 : 2 * (s + 1) * (s + 1 + (c + 1)) + 2 * (s + 1) * ((c + 1) * (a + 1)) +
          ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * ((s + 1) * s) <
        2 * (c + 2) * ((s + 1) ^ 2 * ((a + 2) ^ 2 + 1) + (s + 1) * (a + 2) ^ 2 + 2) := by
      calc _ < 2 * (s + 1) * (s + 1 + (c + 1)) + 2 * (s + 1) * ((c + 1) * (a + 1)) +
              ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * ((s + 1) * s) +
              (2 * a ^ 2 * c * s ^ 2 + 4 * a * c * s ^ 2 + 4 * a ^ 2 * s ^ 2 +
                6 * a ^ 2 * c * s + 4 * c * s ^ 2 + 13 * a * s ^ 2 + 18 * a * c * s +
                12 * a ^ 2 * s + 4 * a ^ 2 * c + 14 * s ^ 2 + 18 * c * s + 43 * a * s +
                14 * a * c + 8 * a ^ 2 + 44 * s + 18 * c + 30 * a + 38) :=
            Nat.lt_add_of_pos_right (by positivity)
        _ = _ := by ring
    linarith [h2, P1, P2, P4, Q1]
  · -- Second dimension count.
    have hS : ∑ l ∈ Finset.range (s + 1),
        ((a + 2) * (d + l * (2 * (c + 1) - 1) + N₂ + (c + 1) + 1) +
          (c + 1) * ((a + 2 - 1) * (2 * l + 2) + 1 - (a + 2))) =
        ∑ l ∈ Finset.range (s + 1),
          (((a + 2) * (d + N₂ + (c + 1) + 1) + (c + 1) * (a + 1)) +
            ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * l) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [key l, hc2]; ring
    rw [hS, ha1]
    have h2 := two_mul_sum_affine ((a + 2) * (d + N₂ + (c + 1) + 1) + (c + 1) * (a + 1))
      ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) s
    have h2' : 2 * ((a + 1) * ∑ l ∈ Finset.range (s + 1),
          (((a + 2) * (d + N₂ + (c + 1) + 1) + (c + 1) * (a + 1)) +
            ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * l)) =
        (a + 1) * (2 * ((a + 2) * (d + N₂ + (c + 1) + 1) + (c + 1) * (a + 1)) * (s + 1) +
          ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * ((s + 1) * s)) := by
      rw [← h2]; ring
    have P1 : (a + 2) * (d + 1) * ((a + 1) * (s + 1 + (c + 1)) + 1) ≤
        (a + 2) * (d + 1) * ((a + 2) * (N₂ + 1)) :=
      Nat.mul_le_mul_left _ hN2b
    have P2 : (a + 1) * (s + 1) * ((a + 2) * N₂) ≤
        (a + 1) * (s + 1) * ((a + 1) * (s + 1 + (c + 1))) :=
      Nat.mul_le_mul_left _ hN2a
    have P4 : ((a + 1) * (c + 1) + 1) *
          ((s + 1) ^ 2 * ((a + 2) ^ 2 + 1) + (s + 1) * (a + 2) ^ 2 + 2) ≤
        ((a + 1) * (c + 1) + 1) * ((a + 2) * (d + 1)) :=
      Nat.mul_le_mul_left _ P3
    have Q2 : 2 * (a + 1) * (s + 1) * ((a + 1) * (s + 1 + (c + 1))) +
          2 * (a + 1) * (s + 1) * ((c + 1) * (2 * a + 3)) +
          (a + 1) * ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * ((s + 1) * s) <
        2 * ((a + 1) * (c + 1) + 1) *
          ((s + 1) ^ 2 * ((a + 2) ^ 2 + 1) + (s + 1) * (a + 2) ^ 2 + 2) := by
      calc _ < 2 * (a + 1) * (s + 1) * ((a + 1) * (s + 1 + (c + 1))) +
              2 * (a + 1) * (s + 1) * ((c + 1) * (2 * a + 3)) +
              (a + 1) * ((a + 2) * (2 * c + 1) + 2 * (c + 1) * (a + 1)) * ((s + 1) * s) +
              (2 * a ^ 3 * c * s ^ 2 + 6 * a ^ 2 * c * s ^ 2 + 2 * a ^ 3 * s ^ 2 +
                6 * a ^ 3 * c * s + 8 * a * c * s ^ 2 + 7 * a ^ 2 * s ^ 2 +
                20 * a ^ 2 * c * s + 6 * a ^ 3 * s + 4 * a ^ 3 * c + 4 * c * s ^ 2 +
                15 * a * s ^ 2 + 28 * a * c * s + 23 * a ^ 2 * s + 14 * a ^ 2 * c +
                4 * a ^ 3 + 14 * s ^ 2 + 14 * c * s + 47 * a * s + 24 * a * c + 16 * a ^ 2 +
                40 * s + 14 * c + 36 * a + 34) :=
            Nat.lt_add_of_pos_right (by positivity)
        _ = _ := by ring
    linarith [h2', P1, P2, P4, Q2]
  · -- First degree bound.
    rw [ha1]
    linarith [hd1, Nat.mul_le_mul_left q hN1a, Nat.zero_le (q * c * a), Nat.zero_le (q * a),
      Nat.zero_le (c * a * a), Nat.zero_le (c * a), Nat.zero_le (a * a)]
  · -- Second degree bound.
    rw [ha1]
    linarith [hd1, Nat.mul_le_mul_left q hN2a, Nat.zero_le (c * a * a), Nat.zero_le (c * a),
      Nat.zero_le (a * a)]

end Langlands.AlgebraicGeometry.LangWeil.Stepanov

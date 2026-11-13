import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic.Linarith

/-! # Simple-root restrictions on repeated type C weights -/

namespace Langlands.TypeCBlockWeights

/-- The first `r` consecutive blocks have length `degree` and weights the
coordinate vectors; all later coordinates have weight zero. -/
def weight (degree r i : ℕ) : Fin r → ℤ :=
  fun k => if k.val * degree ≤ i ∧ i < (k.val + 1) * degree then 1 else 0

/-- Restrict the numbered simple roots `e_i - e_{i+1}` and the final root `2e_i`
to the repeated block weights. -/
def simpleRestriction (degree r : ℕ) {n : ℕ} (i : Fin n) : Fin r → ℤ :=
  if i.val + 1 < n then weight degree r i.val - weight degree r (i.val + 1)
  else 2 • weight degree r i.val

theorem weight_ne_zero_iff {degree r i : ℕ} (hd : 0 < degree) :
    weight degree r i ≠ 0 ↔ i < r * degree := by
  constructor
  · intro h
    by_contra h'
    apply h
    funext k
    have hk := Nat.mul_le_mul_right degree (show k.val + 1 ≤ r by omega)
    simp only [weight, Pi.zero_apply]
    rw [ite_eq_right (by omega)]
  · intro hi hzero
    have hk : i / degree < r := (Nat.div_lt_iff_lt_mul hd).mpr hi
    let k : Fin r := ⟨i / degree, hk⟩
    have hdecomp := Nat.mod_add_div i degree
    have hmod := Nat.mod_lt i hd
    have hlo : k.val * degree ≤ i := Nat.div_mul_le_self i degree
    have hhi : i < (k.val + 1) * degree := by
      dsimp [k]
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (i / degree) degree]
      omega
    have h := congrFun hzero k
    simp [weight, hlo, hhi] at h

theorem difference_ne_zero_iff {degree r i : ℕ} (hd : 0 < degree) :
    weight degree r i - weight degree r (i + 1) ≠ 0 ↔
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ i + 1 = j * degree := by
  constructor
  · intro h
    by_contra hn
    apply h
    funext k
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    apply if_congr ?_ rfl rfl
    have htop : i + 1 ≠ (k.val + 1) * degree :=
      fun heq => hn ⟨k.val + 1, by omega, by omega, heq⟩
    have hbot : i + 1 ≠ k.val * degree := by
      intro heq
      have hk0 : 1 ≤ k.val := by
        by_contra hk
        have : k.val = 0 := by omega
        simp [this] at heq
      exact hn ⟨k.val, hk0, by omega, heq⟩
    omega
  · rintro ⟨j, hj1, hjr, hij⟩ hzero
    let k : Fin r := ⟨j - 1, by omega⟩
    have htop : (k.val + 1) * degree = i + 1 := by
      dsimp [k]
      rw [Nat.sub_add_cancel hj1, ← hij]
    have hlt : k.val * degree < i + 1 := by
      rw [hij]
      exact Nat.mul_lt_mul_of_pos_right (by dsimp [k]; omega) hd
    have h := congrFun hzero k
    simp only [Pi.sub_apply, Pi.zero_apply, weight,
      ite_eq_left (show k.val * degree ≤ i ∧ i < (k.val + 1) * degree by omega),
      ite_eq_right (show ¬ (k.val * degree ≤ i + 1 ∧ i + 1 < (k.val + 1) * degree) by omega)]
      at h
    omega

/-- The nonzero simple restrictions occur exactly at the ends of the first
`r` blocks, including the long root when the final block reaches `n`. -/
theorem simpleRestriction_ne_zero_iff {degree r n : ℕ}
    (hd : 0 < degree) (hrn : r * degree ≤ n) (i : Fin n) :
    simpleRestriction degree r i ≠ 0 ↔
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ r ∧ i.val + 1 = j * degree := by
  unfold simpleRestriction
  split_ifs with hi
  · exact difference_ne_zero_iff hd
  have hin : i.val + 1 = n := by have := i.isLt; omega
  have htwo : 2 • weight degree r i.val ≠ 0 ↔ weight degree r i.val ≠ 0 := by
    constructor
    · intro h hzero
      exact h (by rw [hzero, smul_zero])
    · intro h hzero
      apply h
      funext k
      have hk := congrFun hzero k
      change (2 : ℤ) * weight degree r i.val k = 0 at hk
      change weight degree r i.val k = 0
      omega
  rw [htwo, weight_ne_zero_iff hd]
  constructor
  · intro h
    have heq : n = r * degree := by omega
    have hr : 1 ≤ r := by
      by_contra h'
      have : r = 0 := by omega
      simp [this] at h
    exact ⟨r, hr, le_rfl, hin.trans heq⟩
  · rintro ⟨j, -, hjr, hij⟩
    have hle := Nat.mul_le_mul_right degree hjr
    omega

end Langlands.TypeCBlockWeights

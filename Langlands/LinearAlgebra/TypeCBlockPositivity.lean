import Langlands.LinearAlgebra.TypeCBlockWeights

/-! # A positive functional on repeated type C restrictions -/

namespace Langlands.TypeCBlockWeights

/-- The decreasing positive integer functional on block coordinates. -/
def height (r : ℕ) : (Fin r → ℤ) →+ ℤ where
  toFun v := ∑ k, v k * ((r : ℤ) - k.val)
  map_zero' := by simp
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]

/-- Before the last block, the repeated weight is a single coordinate vector. -/
theorem weight_eq_single {degree r i : ℕ} (hd : 0 < degree) (hi : i < r * degree) :
    weight degree r i = Pi.single ⟨i / degree, (Nat.div_lt_iff_lt_mul hd).mpr hi⟩ 1 := by
  funext k
  have hiff : k.val * degree ≤ i ∧ i < (k.val + 1) * degree ↔ k.val = i / degree := by
    rw [← Nat.le_div_iff_mul_le hd, ← Nat.div_lt_iff_lt_mul hd]
    omega
  simp only [weight, Pi.single_apply, hiff, Fin.ext_iff]

/-- The height of a weight decreases by one between consecutive nonzero blocks. -/
theorem height_weight {degree r i : ℕ} (hd : 0 < degree) :
    height r (weight degree r i) =
      if i < r * degree then (r : ℤ) - (i / degree : ℕ) else 0 := by
  classical
  by_cases hi : i < r * degree
  · rw [ite_eq_left hi, weight_eq_single hd hi]
    change (∑ k : Fin r, (Pi.single ⟨i / degree, (Nat.div_lt_iff_lt_mul hd).mpr hi⟩
      (1 : ℤ) : Fin r → ℤ) k * ((r : ℤ) - k.val)) = _
    simp [Pi.single_apply, ite_mul]
  · have hz : weight degree r i = 0 := by
      by_contra h
      exact hi ((weight_ne_zero_iff hd).mp h)
    rw [hz, map_zero, ite_eq_right hi]

/-- Every nonzero difference of consecutive repeated weights has height one. -/
theorem height_difference {degree r i : ℕ} (hd : 0 < degree)
    (hne : weight degree r i - weight degree r (i + 1) ≠ 0) :
    height r (weight degree r i - weight degree r (i + 1)) = 1 := by
  obtain ⟨j, hj1, hjr, hij⟩ := (difference_ne_zero_iff hd).mp hne
  have hi : i < r * degree := by
    have hle := Nat.mul_le_mul_right degree hjr
    omega
  have hdiv : i / degree = j - 1 := by
    have hlt : (j - 1) * degree < j * degree :=
      Nat.mul_lt_mul_of_pos_right (by omega) hd
    have hlo : j - 1 ≤ i / degree := (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hhi : i / degree < j := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
    omega
  have hdiv' : (i + 1) / degree = j := by
    rw [hij]
    simp [Nat.ne_of_gt hd]
  rw [map_sub, height_weight hd, height_weight hd, ite_eq_left hi, hdiv, hdiv']
  by_cases hj : j < r
  · have hi' : i + 1 < r * degree := by
      rw [hij]
      exact Nat.mul_lt_mul_of_pos_right hj hd
    rw [ite_eq_left hi']
    omega
  · have hjr' : j = r := by omega
    have hi' : ¬ i + 1 < r * degree := by rw [hij, hjr']; omega
    rw [ite_eq_right hi', hjr']
    omega

/-- Every numbered simple restriction is zero or has strictly positive height. -/
theorem simpleRestriction_zero_or_height_pos {degree r n : ℕ}
    (hd : 0 < degree) (i : Fin n) :
    simpleRestriction degree r i = 0 ∨ 0 < height r (simpleRestriction degree r i) := by
  by_cases hz : simpleRestriction degree r i = 0
  · exact Or.inl hz
  right
  unfold simpleRestriction at hz ⊢
  split_ifs at hz ⊢ with hi
  · rw [height_difference hd hz]
    norm_num
  · have hw : weight degree r i.val ≠ 0 := by
      intro h
      exact hz (by rw [h, smul_zero])
    have hlt := (weight_ne_zero_iff hd).mp hw
    have hdiv : i.val / degree < r := (Nat.div_lt_iff_lt_mul hd).mpr hlt
    rw [map_nsmul, height_weight hd, ite_eq_left hlt]
    change 0 < (2 : ℤ) * ((r : ℤ) - (i.val / degree : ℕ))
    omega

end Langlands.TypeCBlockWeights

import Langlands.Algebra.RankOneRelationIdentities

/-! # The Weyl element of the rank-one open-cell relation

Further abstract consequences of `RankOneRelation.Data`: the square of `w(1)` and the action of
`w(1)` on `h` by conjugation. -/

namespace Langlands.Algebra.RankOneRelation

namespace Data

variable {k H : Type*} [Field k] [Group H] (D : Data k H)

/-- `w(c)⁻¹ = w(-c)`. -/
theorem w_inv (c : k) : (D.w c)⁻¹ = D.w (-c) := by
  simp only [w, mul_inv_rev, ← D.xm_neg, ← D.xp_neg, inv_neg, neg_neg]
  group

/-- `w(1)² = h(-1)`. -/
theorem w_one_mul_self : D.w 1 * D.w 1 = D.h (-1) := by
  have h := D.w_mul_w_one_inv (-1)
  have hm : D.w (((-1 : kˣ) : k)) = (D.w 1)⁻¹ := by
    rw [D.w_inv, Units.val_neg, Units.val_one]
  rw [hm] at h
  have h2 : D.h (-1) * D.h (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  calc D.w 1 * D.w 1 = ((D.w 1)⁻¹ * (D.w 1)⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
    _ = (D.h (-1))⁻¹ := by rw [h]
    _ = D.h (-1) := by rw [inv_eq_of_mul_eq_one_right h2]

/-- Conjugation by `w(1)` inverts `h`: `w(1) h(c) w(1)⁻¹ = h(c)⁻¹`. -/
theorem w_one_conj_h (c : kˣ) : D.w 1 * D.h c * (D.w 1)⁻¹ = (D.h c)⁻¹ := by
  have hc := D.w_eq_h_mul_w_one c
  have hnc := D.w_eq_h_mul_w_one (-c)
  have hinv := D.w_inv (c : k)
  rw [hc, ← Units.val_neg, hnc] at hinv
  have hm : D.h (-c) = D.h c * (D.w 1 * D.w 1) := by
    rw [D.w_one_mul_self, ← map_mul, mul_neg_one]
  rw [hm] at hinv
  have h4 : D.w 1 * D.w 1 * (D.w 1 * D.w 1) = 1 := by
    rw [D.w_one_mul_self, ← map_mul, neg_one_mul, neg_neg, map_one]
  have h1 : D.w 1 * D.h c * D.w 1 * D.w 1 * D.w 1 = (D.h c)⁻¹ := by
    calc D.w 1 * D.h c * D.w 1 * D.w 1 * D.w 1
        = D.w 1 * (D.h c * (D.w 1 * D.w 1) * D.w 1) := by group
      _ = D.w 1 * (D.h c * D.w 1)⁻¹ := by rw [hinv]
      _ = (D.h c)⁻¹ := by group
  calc D.w 1 * D.h c * (D.w 1)⁻¹
      = (D.w 1 * D.h c * D.w 1 * D.w 1 * D.w 1) * (D.w 1 * D.w 1 * (D.w 1 * D.w 1))⁻¹ := by
        group
    _ = (D.h c)⁻¹ := by rw [h1, h4, inv_one, mul_one]

/-- The product of two Weyl-type elements `h(c₁) w(1)` and `h(c₂) w(1)` lies in the image of
`h`: it equals `h(-c₁ c₂⁻¹)`. -/
theorem h_mul_w_mul_h_mul_w (c₁ c₂ : kˣ) :
    D.h c₁ * D.w 1 * (D.h c₂ * D.w 1) = D.h (-(c₁ * c₂⁻¹)) := by
  have hconj := D.w_one_conj_h c₂
  calc D.h c₁ * D.w 1 * (D.h c₂ * D.w 1)
      = D.h c₁ * (D.w 1 * D.h c₂ * (D.w 1)⁻¹) * (D.w 1 * D.w 1) := by group
    _ = D.h c₁ * (D.h c₂)⁻¹ * D.h (-1) := by rw [hconj, D.w_one_mul_self]
    _ = D.h (-(c₁ * c₂⁻¹)) := by
        rw [← map_inv, ← map_mul, ← map_mul, mul_neg_one]

end Data

end Langlands.Algebra.RankOneRelation

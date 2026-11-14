import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Identities from the rank-one open-cell relation

Abstract group-theoretic consequences of the relation
`x₊(X) x₋(Y) = x₋(Y/u) h(u) x₊(X/u)`, `u = 1 + XY`, satisfied by linked root
parametrizations of a split rank-one group. -/

namespace Langlands.Algebra.RankOneRelation

/-- Hypotheses: `xp` and `xm` are additive into `H`, `h` is multiplicative, `h t`
scales `xm` by `t⁻²`, and the open-cell relation holds whenever `1 + XY` is a unit. -/
structure Data (k H : Type*) [Field k] [Group H] where
  xp : k → H
  xm : k → H
  h : kˣ →* H
  xp_add : ∀ a b, xp (a + b) = xp a * xp b
  xm_add : ∀ a b, xm (a + b) = xm a * xm b
  h_xm : ∀ (t : kˣ) (c : k), h t * xm c * (h t)⁻¹ = xm ((t : k)⁻¹ ^ 2 * c)
  relation : ∀ (X Y : k) (u : kˣ), (u : k) = 1 + X * Y →
    xp X * xm Y = xm ((u : k)⁻¹ * Y) * h u * xp ((u : k)⁻¹ * X)

namespace Data

variable {k H : Type*} [Field k] [Group H] (D : Data k H)

theorem xp_zero : D.xp 0 = 1 := by
  have h := D.xp_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem xm_zero : D.xm 0 = 1 := by
  have h := D.xm_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem xp_neg (a : k) : D.xp (-a) = (D.xp a)⁻¹ := by
  have h := D.xp_add a (-a)
  rw [add_neg_cancel, D.xp_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem xm_neg (a : k) : D.xm (-a) = (D.xm a)⁻¹ := by
  have h := D.xm_add a (-a)
  rw [add_neg_cancel, D.xm_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Commuting `h t` past `xm c`. -/
theorem h_mul_xm (t : kˣ) (c : k) : D.h t * D.xm c = D.xm ((t : k)⁻¹ ^ 2 * c) * D.h t := by
  rw [← D.h_xm t c]
  group

/-- `h(u)` is the word `x₋(u⁻¹(u-1))⁻¹ x₊(1) x₋(u-1) x₊(u⁻¹)⁻¹` in the root elements. -/
theorem h_eq_word (u : kˣ) :
    D.h u = (D.xm ((u : k)⁻¹ * ((u : k) - 1)))⁻¹ * D.xp 1 * D.xm ((u : k) - 1) *
      (D.xp (u : k)⁻¹)⁻¹ := by
  have hrel := D.relation 1 ((u : k) - 1) u (by ring)
  rw [mul_one] at hrel
  rw [mul_assoc (D.xm _)⁻¹, mul_assoc (D.xm _)⁻¹, hrel]
  group

/-- The Weyl-type element `w(c) = x₋(-c⁻¹) x₊(c) x₋(-c⁻¹)`. -/
def w (c : k) : H := D.xm (-c⁻¹) * D.xp c * D.xm (-c⁻¹)

/-- `w(v) w(1)⁻¹ = h(v)` for every unit `v`. -/
theorem w_mul_w_one_inv (v : kˣ) : D.w v * (D.w 1)⁻¹ = D.h v := by
  have hv : (v : k) ≠ 0 := v.ne_zero
  have hrel := D.relation (v : k) (1 - (v : k)⁻¹) v (by field_simp; ring)
  have hw1 : (D.w 1)⁻¹ = D.xm 1 * D.xp (-1) * D.xm 1 := by
    simp only [w, inv_one, mul_inv_rev, ← D.xm_neg, ← D.xp_neg, neg_neg]
    group
  rw [hw1, w]
  calc D.xm (-(v : k)⁻¹) * D.xp v * D.xm (-(v : k)⁻¹) * (D.xm 1 * D.xp (-1) * D.xm 1)
      = D.xm (-(v : k)⁻¹) * (D.xp v * D.xm (1 - (v : k)⁻¹)) * D.xp (-1) * D.xm 1 := by
        rw [sub_eq_neg_add, D.xm_add]; group
    _ = D.xm (-(v : k)⁻¹) * D.xm ((v : k)⁻¹ * (1 - (v : k)⁻¹)) * (D.h v *
          (D.xp ((v : k)⁻¹ * v) * D.xp (-1))) * D.xm 1 := by
        rw [hrel]; group
    _ = D.xm (-(v : k)⁻¹) * D.xm ((v : k)⁻¹ * (1 - (v : k)⁻¹)) * (D.h v * D.xm 1) := by
        rw [← D.xp_add, inv_mul_cancel₀ hv, add_neg_cancel, D.xp_zero]; group
    _ = D.xm (-(v : k)⁻¹ + (v : k)⁻¹ * (1 - (v : k)⁻¹) + (v : k)⁻¹ ^ 2 * 1) * D.h v := by
        rw [D.h_mul_xm, D.xm_add, D.xm_add]; group
    _ = D.h v := by
        rw [show -(v : k)⁻¹ + (v : k)⁻¹ * (1 - (v : k)⁻¹) + (v : k)⁻¹ ^ 2 * 1 = 0 by ring,
          D.xm_zero, one_mul]

/-- `w(v) = h(v) w(1)`. -/
theorem w_eq_h_mul_w_one (v : kˣ) : D.w v = D.h v * D.w 1 := by
  rw [← D.w_mul_w_one_inv v]; group

/-- The open cell `x₋(k) h(kˣ) x₊(k)`. -/
def InCell (g : H) : Prop := ∃ (Y : k) (t : kˣ) (X : k), g = D.xm Y * D.h t * D.xp X

/-- If `x₋(e₁) x₊(1) x₋(e₂)` and its inverse both lie outside the open cell, then
`e₁ = e₂ = -1`; that is, the element is `w(1)`. -/
theorem eq_neg_one_of_not_inCell (e₁ e₂ : k)
    (hn : ¬ D.InCell (D.xm e₁ * D.xp 1 * D.xm e₂))
    (hn' : ¬ D.InCell (D.xm e₁ * D.xp 1 * D.xm e₂)⁻¹) :
    e₁ = -1 ∧ e₂ = -1 := by
  constructor
  · by_contra he
    have hu : (1 : k) + -1 * -e₁ ≠ 0 := by
      intro h0; apply he; linear_combination h0
    set u : kˣ := Units.mk0 _ hu
    have hrel := D.relation (-1) (-e₁) u rfl
    apply hn'
    refine ⟨-e₂ + (u : k)⁻¹ * -e₁, u, (u : k)⁻¹ * -1, ?_⟩
    simp only [mul_inv_rev, ← D.xm_neg, ← D.xp_neg]
    rw [D.xm_add, hrel]
    group
  · by_contra he
    have hu : (1 : k) + 1 * e₂ ≠ 0 := by
      intro h0; apply he; linear_combination h0
    set u : kˣ := Units.mk0 _ hu
    have hrel := D.relation 1 e₂ u rfl
    apply hn
    refine ⟨e₁ + (u : k)⁻¹ * e₂, u, (u : k)⁻¹ * 1, ?_⟩
    rw [D.xm_add, mul_assoc (D.xm e₁), hrel]
    group

end Data

end Langlands.Algebra.RankOneRelation

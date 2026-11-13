import Mathlib

/-!
# Degree boxes for bivariate polynomials

For `P : F[X][Y]` (outer variable `Y`, inner variable `X`) and integers `a b`,
`InBox a b P` says that every monomial `X^i Y^j` occurring in `P` has `i ≤ a`
and `j ≤ b`.  Negative bounds force `P = 0`.  Boxes are closed under sums and
multiply additively.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

variable {F : Type u} [CommRing F]

/-- Every monomial `X^i Y^j` of `P` has `i ≤ a` and `j ≤ b`. -/
def InBox (a b : ℤ) (P : Polynomial (Polynomial F)) : Prop :=
  ∀ j i : ℕ, (P.coeff j).coeff i ≠ 0 → (i : ℤ) ≤ a ∧ (j : ℤ) ≤ b

theorem inBox_zero (a b : ℤ) : InBox a b (0 : Polynomial (Polynomial F)) := by
  intro j i h; simp at h

theorem InBox.mono {a b a' b' : ℤ} {P : Polynomial (Polynomial F)} (h : InBox a b P)
    (ha : a ≤ a') (hb : b ≤ b') : InBox a' b' P := by
  intro j i hji
  obtain ⟨h1, h2⟩ := h j i hji
  exact ⟨h1.trans ha, h2.trans hb⟩

theorem InBox.add {a b : ℤ} {P Q : Polynomial (Polynomial F)} (hP : InBox a b P)
    (hQ : InBox a b Q) : InBox a b (P + Q) := by
  intro j i h
  simp only [coeff_add] at h
  by_cases h1 : (P.coeff j).coeff i = 0
  · rw [h1, zero_add] at h; exact hQ j i h
  · exact hP j i h1

theorem InBox.neg {a b : ℤ} {P : Polynomial (Polynomial F)} (hP : InBox a b P) :
    InBox a b (-P) := by
  intro j i h
  simp only [coeff_neg, neg_ne_zero] at h
  exact hP j i h

theorem InBox.sub {a b : ℤ} {P Q : Polynomial (Polynomial F)} (hP : InBox a b P)
    (hQ : InBox a b Q) : InBox a b (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

theorem inBox_sum {ι : Type*} (s : Finset ι) {a b : ℤ} (P : ι → Polynomial (Polynomial F))
    (h : ∀ k ∈ s, InBox a b (P k)) : InBox a b (∑ k ∈ s, P k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inBox_zero a b
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact (h k (Finset.mem_insert_self _ _)).add
      (ih (fun k' hk' => h k' (Finset.mem_insert_of_mem hk')))

theorem InBox.mul {a b a' b' : ℤ} {P Q : Polynomial (Polynomial F)} (hP : InBox a b P)
    (hQ : InBox a' b' Q) : InBox (a + a') (b + b') (P * Q) := by
  intro j i h
  rw [coeff_mul, finsetSum_coeff] at h
  obtain ⟨⟨j1, j2⟩, hj, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_mul] at h
  obtain ⟨⟨i1, i2⟩, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hj hi
  dsimp only at h
  obtain ⟨hP1, hP2⟩ := hP j1 i1 (left_ne_zero_of_mul h)
  obtain ⟨hQ1, hQ2⟩ := hQ j2 i2 (right_ne_zero_of_mul h)
  subst hj hi
  push_cast
  constructor <;> linarith

theorem InBox.smul_C_C {a b : ℤ} {P : Polynomial (Polynomial F)} (hP : InBox a b P) (r : F) :
    InBox a b (C (C r) * P) := by
  intro j i h
  rw [coeff_C_mul, coeff_C_mul] at h
  exact hP j i (right_ne_zero_of_mul h)

theorem inBox_C_C (r : F) : InBox 0 0 (C (C r) : Polynomial (Polynomial F)) := by
  intro j i h
  rw [coeff_C] at h
  split_ifs at h with hj
  · rw [coeff_C] at h
    split_ifs at h with hi
    · subst hj hi; simp
    · exact absurd rfl h
  · exact absurd (by simp) h

theorem inBox_one : InBox 0 0 (1 : Polynomial (Polynomial F)) := by
  simpa using inBox_C_C (F := F) 1

theorem inBox_C_X : InBox 1 0 (C X : Polynomial (Polynomial F)) := by
  intro j i h
  rw [coeff_C] at h
  split_ifs at h with hj
  · rw [coeff_X] at h
    split_ifs at h with hi
    · subst hj hi; simp
    · exact absurd rfl h
  · exact absurd (by simp) h

theorem inBox_X : InBox 0 1 (X : Polynomial (Polynomial F)) := by
  intro j i h
  rw [coeff_X] at h
  split_ifs at h with hj
  · rw [coeff_one] at h
    split_ifs at h with hi
    · subst hj hi; simp
    · exact absurd rfl h
  · exact absurd (by simp) h

theorem InBox.pow {a b : ℤ} {P : Polynomial (Polynomial F)} (hP : InBox a b P) (k : ℕ) :
    InBox (k * a) (k * b) (P ^ k) := by
  induction k with
  | zero => simpa using inBox_one
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul hP
    push_cast
    convert this using 1 <;> ring

theorem inBox_prod {ι : Type*} (s : Finset ι) (a b : ι → ℤ) (P : ι → Polynomial (Polynomial F))
    (h : ∀ k ∈ s, InBox (a k) (b k) (P k)) :
    InBox (∑ k ∈ s, a k) (∑ k ∈ s, b k) (∏ k ∈ s, P k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inBox_one
  | @insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.sum_insert hk]
    exact (h k (Finset.mem_insert_self _ _)).mul
      (ih (fun k' hk' => h k' (Finset.mem_insert_of_mem hk')))

theorem inBox_iff_of_nonneg {a b : ℕ} {P : Polynomial (Polynomial F)} :
    InBox a b P ↔ P.natDegree ≤ b ∧ ∀ j, (P.coeff j).natDegree ≤ a := by
  constructor
  · intro h
    refine ⟨?_, fun j => ?_⟩
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      by_contra hne
      obtain ⟨i, hi⟩ : ∃ i, (P.coeff j).coeff i ≠ 0 := by
        by_contra! H
        exact hne (Polynomial.ext (by simpa using H))
      have := (h j i hi).2
      omega
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      by_contra hne
      have := (h j i hne).1
      omega
  · rintro ⟨h1, h2⟩ j i h
    constructor
    · have := le_natDegree_of_ne_zero h
      have := h2 j
      omega
    · have hj : P.coeff j ≠ 0 := fun h0 => h (by simp [h0])
      have := le_natDegree_of_ne_zero hj
      omega

theorem InBox.eq_zero_of_neg_left {a b : ℤ} {P : Polynomial (Polynomial F)} (h : InBox a b P)
    (ha : a < 0) : P = 0 := by
  ext j i
  by_contra hne
  have := (h j i hne).1
  simp only [coeff_zero] at *
  omega

theorem InBox.eq_zero_of_neg_right {a b : ℤ} {P : Polynomial (Polynomial F)} (h : InBox a b P)
    (hb : b < 0) : P = 0 := by
  ext j i
  by_contra hne
  have := (h j i hne).2
  simp only [coeff_zero] at *
  omega

end Langlands.AlgebraicGeometry.LangWeil.Stepanov

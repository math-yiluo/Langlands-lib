import Langlands.Global.RankinSelberg.ProjectionExpansion
import Langlands.Automorphic.CuspidalWhittaker.Unipotent

/-! # Rectangular, column, row and middle-block points for the dual expansion -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global
open Langlands.Automorphic.CuspidalWhittaker (sqZeroUnit sqZeroUnit_val)

section Matrices

variable {R : Type*} [CommRing R]

/-- A product of matrices vanishes when no middle index supports both factors. -/
theorem mul_eq_zero_of_support {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (P Q : Fin n → Prop)
    (hA : ∀ a l, A a l ≠ 0 → P l) (hB : ∀ l b, B l b ≠ 0 → Q l)
    (hPQ : ∀ l, P l → Q l → False) : A * B = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h1 : A a l = 0
  · rw [h1, zero_mul]
  by_cases h2 : B l b = 0
  · rw [h2, mul_zero]
  exact (hPQ l (hA a l h1) (hB l b h2)).elim

variable (m K : ℕ)

/-- The rectangular-column matrix: rows `m, …, m+K-1` carry `x` in the columns `< m` and `c` in
the last column `m+K`. -/
def xcMat (x : Fin K × Fin m → R) (c : Fin K → R) :
    Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R :=
  fun a b => if ha : m ≤ (a : ℕ) ∧ (a : ℕ) < m + K then
    (if hb : (b : ℕ) < m then x (⟨(a : ℕ) - m, by omega⟩, ⟨b, hb⟩)
      else if (b : ℕ) = m + K then c ⟨(a : ℕ) - m, by omega⟩ else 0)
    else 0

/-- The row matrix: the last row `m+K` carries `b` in the columns `< m`. -/
def rowMat (b : Fin m → R) : Matrix (Fin (m + K + 1)) (Fin (m + K + 1)) R :=
  fun a j => if (a : ℕ) = m + K then (if hj : (j : ℕ) < m then b ⟨j, hj⟩ else 0) else 0

variable {m K}

theorem xcMat_support_left (x : Fin K × Fin m → R) (c : Fin K → R) (a l : Fin (m + K + 1))
    (h : xcMat m K x c a l ≠ 0) : (l : ℕ) < m ∨ (l : ℕ) = m + K := by
  simp only [xcMat] at h
  split_ifs at h with h1 h2 h3
  · exact Or.inl h2
  · exact Or.inr h3
  · exact absurd rfl h
  · exact absurd rfl h

theorem xcMat_support_right (x : Fin K × Fin m → R) (c : Fin K → R) (l b : Fin (m + K + 1))
    (h : xcMat m K x c l b ≠ 0) : m ≤ (l : ℕ) ∧ (l : ℕ) < m + K := by
  simp only [xcMat] at h
  split_ifs at h with h1
  · exact h1
  · exact h1
  · exact h1
  · exact absurd rfl h

theorem rowMat_support_left (b : Fin m → R) (a l : Fin (m + K + 1))
    (h : rowMat m K b a l ≠ 0) : (l : ℕ) < m := by
  simp only [rowMat] at h
  split_ifs at h with h1 h2
  · exact h2
  · exact absurd rfl h
  · exact absurd rfl h

theorem rowMat_support_right (b : Fin m → R) (l j : Fin (m + K + 1))
    (h : rowMat m K b l j ≠ 0) : (l : ℕ) = m + K := by
  simp only [rowMat] at h
  split_ifs at h with h1
  · exact h1
  · exact h1
  · exact absurd rfl h

theorem xcMat_mul_xcMat (x x' : Fin K × Fin m → R) (c c' : Fin K → R) :
    xcMat m K x c * xcMat m K x' c' = 0 :=
  mul_eq_zero_of_support _ _ _ _ (xcMat_support_left x c) (xcMat_support_right x' c')
    (fun l h1 h2 => by omega)

theorem rowMat_mul_xcMat (b : Fin m → R) (x : Fin K × Fin m → R) (c : Fin K → R) :
    rowMat m K b * xcMat m K x c = 0 :=
  mul_eq_zero_of_support _ _ _ _ (rowMat_support_left b) (xcMat_support_right x c)
    (fun l h1 h2 => by omega)

theorem rowMat_mul_rowMat (b b' : Fin m → R) : rowMat m K b * rowMat m K b' = 0 :=
  mul_eq_zero_of_support _ _ _ _ (rowMat_support_left b) (rowMat_support_right b')
    (fun l h1 h2 => by omega)

theorem xcMat_add (x x' : Fin K × Fin m → R) (c c' : Fin K → R) :
    xcMat m K (x + x') (c + c') = xcMat m K x c + xcMat m K x' c' := by
  ext a b
  simp only [xcMat, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem rowMat_add (b b' : Fin m → R) : rowMat m K (b + b') = rowMat m K b + rowMat m K b' := by
  ext a j
  simp only [rowMat, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

theorem xcMat_zero : xcMat m K (0 : Fin K × Fin m → R) 0 = 0 := by
  ext a b
  simp only [xcMat, Pi.zero_apply, Matrix.zero_apply]
  split_ifs <;> rfl

theorem rowMat_zero : rowMat m K (0 : Fin m → R) = 0 := by
  ext a j
  simp only [rowMat, Pi.zero_apply, Matrix.zero_apply]
  split_ifs <;> rfl

/-- The outer product `c ⊗ b` of a column and a row. -/
def outerRect (c : Fin K → R) (b : Fin m → R) : Fin K × Fin m → R := fun p => c p.1 * b p.2

theorem xcMat_mul_rowMat (x : Fin K × Fin m → R) (c : Fin K → R) (b : Fin m → R) :
    xcMat m K x c * rowMat m K b = xcMat m K (outerRect c b) 0 := by
  ext a j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨m + K, by omega⟩ : Fin (m + K + 1))]
  · simp only [xcMat, rowMat, outerRect, Pi.zero_apply]
    by_cases ha : m ≤ (a : ℕ) ∧ (a : ℕ) < m + K
    · by_cases hj : (j : ℕ) < m
      · simp [ha, hj]
      · simp [ha, hj]
    · simp [ha]
  · intro l _ hl
    by_cases h : rowMat m K b l j = 0
    · rw [h, mul_zero]
    · exact absurd (Fin.ext (rowMat_support_right b l j h)) hl
  · intro h
    exact absurd (Finset.mem_univ _) h

end Matrices

section MiddleBlock

variable {R : Type*} [CommRing R]

/-- `A ↦ diag(I_m, A)`, the lower-right block embedding. -/
def lrMatrix (m K : ℕ) :
    Matrix (Fin K) (Fin K) R →* Matrix (Fin (m + K)) (Fin (m + K)) R where
  toFun A := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) R) 0 0 A)
  map_one' := by simp
  map_mul' A B := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem lrMatrix_apply (m K : ℕ) (A : Matrix (Fin K) (Fin K) R) (a b : Fin (m + K)) :
    lrMatrix m K A a b =
      if ha : m ≤ (a : ℕ) then
        (if hb : m ≤ (b : ℕ) then A ⟨(a : ℕ) - m, by omega⟩ ⟨(b : ℕ) - m, by omega⟩ else 0)
      else (if a = b then 1 else 0) := by
  simp only [lrMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  refine Fin.addCases (fun a₀ => ?_) (fun a₁ => ?_) a <;>
    refine Fin.addCases (fun b₀ => ?_) (fun b₁ => ?_) b
  · have := a₀.isLt
    have := b₀.isLt
    simp [Fin.ext_iff, Matrix.one_apply]
  · have := a₀.isLt
    have := b₁.isLt
    simp only [Fin.val_castAdd]
    rw [dite_eq_right (by omega)]
    have hne : Fin.castAdd K a₀ ≠ Fin.natAdd m b₁ := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    simp [hne]
  · have := a₁.isLt
    have := b₀.isLt
    simp
  · simp

/-- The lower-right block embedding of invertible matrices. -/
def lrGL (m K : ℕ) :
    Matrix.GeneralLinearGroup (Fin K) R →* Matrix.GeneralLinearGroup (Fin (m + K)) R :=
  Units.map (lrMatrix m K)

end MiddleBlock

variable (F : Type u) [Field F] [NumberField F]

local instance dualPointsSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualPointsSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Points

variable {m K : ℕ}

/-- The point `1 + xcMat x c` of `GL_(m+K+1)(𝔸)`. -/
def xcPoint (x : Fin K × Fin m → Adeles F) (c : Fin K → Adeles F) : Points F (m + K + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).symm
    (sqZeroUnit (xcMat m K x c) (xcMat_mul_xcMat x x c c))

/-- The point `1 + rowMat b` of `GL_(m+K+1)(𝔸)`. -/
def rowPoint (b : Fin m → Adeles F) : Points F (m + K + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (m + K + 1)).symm
    (sqZeroUnit (rowMat m K b) (rowMat_mul_rowMat b b))

/-- The point `diag(I_m, u, 1)` of `GL_(m+K+1)(𝔸)` for `u ∈ GL_K(𝔸)`. -/
def midPoint (u : Points F K) : Points F (m + K + 1) :=
  pad F (Nat.le_succ (m + K)) ((GeneralLinearGroupPoints.adelicEquiv F (m + K)).symm
    (lrGL m K (GeneralLinearGroupPoints.adelicEquiv F K u)))

theorem pointMatrix_xcPoint (x : Fin K × Fin m → Adeles F) (c : Fin K → Adeles F) :
    pointMatrix F (xcPoint F x c) = 1 + xcMat m K x c := by
  simp only [pointMatrix, xcPoint, MulEquiv.apply_symm_apply, sqZeroUnit_val]

theorem pointMatrix_rowPoint (b : Fin m → Adeles F) :
    pointMatrix F (rowPoint F (K := K) b) = 1 + rowMat m K b := by
  simp only [pointMatrix, rowPoint, MulEquiv.apply_symm_apply, sqZeroUnit_val]

theorem point_ext {n : ℕ} {g h : Points F n} (hgh : pointMatrix F g = pointMatrix F h) : g = h := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  exact Units.ext hgh

theorem pointMatrix_mul {n : ℕ} (g h : Points F n) :
    pointMatrix F (g * h) = pointMatrix F g * pointMatrix F h := by
  simp only [pointMatrix, map_mul, Units.val_mul]

theorem xcPoint_mul (x x' : Fin K × Fin m → Adeles F) (c c' : Fin K → Adeles F) :
    xcPoint F x c * xcPoint F x' c' = xcPoint F (x + x') (c + c') := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_xcPoint, pointMatrix_xcPoint, pointMatrix_xcPoint,
    xcMat_add, add_mul, one_mul, mul_add, mul_one, xcMat_mul_xcMat, add_zero]
  abel

theorem rowPoint_mul (b b' : Fin m → Adeles F) :
    rowPoint F (K := K) b * rowPoint F b' = rowPoint F (b + b') := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_rowPoint, pointMatrix_rowPoint, pointMatrix_rowPoint,
    rowMat_add, add_mul, one_mul, mul_add, mul_one, rowMat_mul_rowMat, add_zero]
  abel

theorem xcPoint_zero : xcPoint F (m := m) (K := K) 0 0 = 1 := by
  apply point_ext
  rw [pointMatrix_xcPoint, xcMat_zero, add_zero]
  simp [pointMatrix]

theorem rowPoint_zero : rowPoint F (m := m) (K := K) 0 = 1 := by
  apply point_ext
  rw [pointMatrix_rowPoint, rowMat_zero, add_zero]
  simp [pointMatrix]

/-- Moving a row point past a rectangular-column point shears the rectangle by `c ⊗ b`. -/
theorem rowPoint_mul_xcPoint (b : Fin m → Adeles F) (x : Fin K × Fin m → Adeles F)
    (c : Fin K → Adeles F) :
    rowPoint F b * xcPoint F x c = xcPoint F (x - outerRect c b) c * rowPoint F b := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_mul, pointMatrix_rowPoint, pointMatrix_xcPoint,
    pointMatrix_xcPoint]
  have hsplit : xcMat m K (x - outerRect c b) c =
      xcMat m K x c - xcMat m K (outerRect c b) 0 := by
    rw [eq_sub_iff_add_eq, ← xcMat_add]
    congr 1
    · abel
    · simp
  have hz : outerRect (0 : Fin K → Adeles F) b = 0 := by
    funext p; simp [outerRect]
  rw [hsplit]
  simp only [add_mul, mul_add, one_mul, mul_one, sub_mul, rowMat_mul_xcMat, xcMat_mul_rowMat,
    hz, xcMat_zero]
  abel

end Points

section Sums

variable {R : Type*} [AddCommMonoid R]

/-- A sum over `Fin (m+K+1)` of a function supported on the middle block `[m, m+K)`. -/
theorem sum_middle {m K : ℕ} (f : Fin (m + K + 1) → R)
    (hf : ∀ l : Fin (m + K + 1), ¬(m ≤ (l : ℕ) ∧ (l : ℕ) < m + K) → f l = 0) :
    ∑ l, f l = ∑ k : Fin K, f ⟨m + k, by omega⟩ := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_add]
  have h1 : ∑ i : Fin m, f (Fin.castSucc (Fin.castAdd K i)) = 0 :=
    Finset.sum_eq_zero fun i _ => hf _ (by simp)
  have h2 : f (Fin.last (m + K)) = 0 := hf _ (by simp)
  rw [h1, h2, zero_add, add_zero]
  rfl

end Sums

section MiddleEntries

variable (F : Type u) [Field F] [NumberField F]
variable {m K : ℕ}

/-- The entries of `diag(I_m, u, 1)`. -/
theorem pointMatrix_midPoint (u : Points F K) (a b : Fin (m + K + 1)) :
    pointMatrix F (midPoint F (m := m) u) a b =
      if h : m ≤ (a : ℕ) ∧ (a : ℕ) < m + K ∧ m ≤ (b : ℕ) ∧ (b : ℕ) < m + K then
        pointMatrix F u ⟨(a : ℕ) - m, by omega⟩ ⟨(b : ℕ) - m, by omega⟩
      else (if a = b then 1 else 0) := by
  simp only [pointMatrix, midPoint, adelicEquiv_pad, MulEquiv.apply_symm_apply]
  rw [padGL_apply]
  by_cases ha : (a : ℕ) < m + K
  · rw [dite_eq_left ha]
    by_cases hb : (b : ℕ) < m + K
    · rw [dite_eq_left hb]
      change lrMatrix m K _ _ _ = _
      rw [lrMatrix_apply]
      by_cases ham : m ≤ (a : ℕ)
      · rw [dite_eq_left ham]
        by_cases hbm : m ≤ (b : ℕ)
        · rw [dite_eq_left hbm, dite_eq_left ⟨ham, ha, hbm, hb⟩]
        · rw [dite_eq_right hbm, dite_eq_right (by omega), ite_eq_right (fun h => by subst h; omega)]
      · rw [dite_eq_right ham, dite_eq_right (by omega)]
        by_cases hab : a = b
        · subst hab; simp
        · rw [ite_eq_right (fun h => hab (Fin.ext (by simpa using congrArg Fin.val h))), ite_eq_right hab]
    · rw [dite_eq_right hb, dite_eq_right (by omega), ite_eq_right (fun h => by subst h; omega)]
  · rw [dite_eq_right ha, dite_eq_right (by omega)]

end MiddleEntries

section Commute

variable {R : Type*} [CommRing R] {n : ℕ}

/-- A matrix that is the identity outside the index set `S` fixes, on the right, matrices whose
columns are supported outside `S`. -/
theorem mul_eq_self_of_cols (N M : Matrix (Fin n) (Fin n) R) (S : Fin n → Prop)
    (hM : ∀ a l, (¬S a ∨ ¬S l) → M a l = (1 : Matrix (Fin n) (Fin n) R) a l)
    (hN : ∀ a l, N a l ≠ 0 → ¬S l) : N * M = N := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · by_cases hab : N a b = 0
    · rw [hab, zero_mul]
    · rw [hM b b (Or.inl (hN a b hab)), Matrix.one_apply_eq, mul_one]
  · intro l _ hlb
    by_cases hal : N a l = 0
    · rw [hal, zero_mul]
    · rw [hM l b (Or.inl (hN a l hal)), Matrix.one_apply_ne hlb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Same, on the left, for matrices whose rows are supported outside `S`. -/
theorem mul_eq_self_of_rows (M N : Matrix (Fin n) (Fin n) R) (S : Fin n → Prop)
    (hM : ∀ a l, (¬S a ∨ ¬S l) → M a l = (1 : Matrix (Fin n) (Fin n) R) a l)
    (hN : ∀ l b, N l b ≠ 0 → ¬S l) : M * N = N := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · by_cases hab : N a b = 0
    · rw [hab, mul_zero]
    · rw [hM a a (Or.inl (hN a b hab)), Matrix.one_apply_eq, one_mul]
  · intro l _ hla
    by_cases hlb : N l b = 0
    · rw [hlb, mul_zero]
    · rw [hM a l (Or.inr (hN l b hlb)), Matrix.one_apply_ne (Ne.symm hla), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Commute

section MiddleAlgebra

variable (F : Type u) [Field F] [NumberField F]
variable {m K : ℕ}

theorem pointMatrix_midPoint_of_not (u : Points F K) (a l : Fin (m + K + 1))
    (h : ¬(m ≤ (a : ℕ) ∧ (a : ℕ) < m + K) ∨ ¬(m ≤ (l : ℕ) ∧ (l : ℕ) < m + K)) :
    pointMatrix F (midPoint F (m := m) u) a l = (1 : Matrix (Fin (m + K + 1)) _ (Adeles F)) a l := by
  rw [pointMatrix_midPoint, dite_eq_right (by omega), Matrix.one_apply]

/-- The middle-block point commutes with row points. -/
theorem rowPoint_mul_midPoint (b : Fin m → Adeles F) (u : Points F K) :
    rowPoint F b * midPoint F u = midPoint F u * rowPoint F b := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_mul, pointMatrix_rowPoint, add_mul, one_mul, mul_add, mul_one]
  have hS := pointMatrix_midPoint_of_not F (m := m) u
  rw [mul_eq_self_of_cols _ _ (fun l : Fin (m + K + 1) => m ≤ (l : ℕ) ∧ (l : ℕ) < m + K) hS
      (fun a l h => by have := rowMat_support_left b a l h; omega),
    mul_eq_self_of_rows _ _ (fun l : Fin (m + K + 1) => m ≤ (l : ℕ) ∧ (l : ℕ) < m + K) hS
      (fun l j h => by have := rowMat_support_right b l j h; omega)]

/-- `U · x` on the rows of a rectangular matrix. -/
def rowMulRect (U : Matrix (Fin K) (Fin K) (Adeles F)) (x : Fin K × Fin m → Adeles F) :
    Fin K × Fin m → Adeles F := fun p => ∑ k : Fin K, U p.1 k * x (k, p.2)

/-- Conjugating a rectangular-column point by `diag(I_m, u, 1)`. -/
theorem midPoint_mul_xcPoint (u : Points F K) (x : Fin K × Fin m → Adeles F)
    (c : Fin K → Adeles F) :
    midPoint F u * xcPoint F x c =
      xcPoint F (rowMulRect F (pointMatrix F u) x) (Matrix.mulVec (pointMatrix F u) c) *
        midPoint F u := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_mul, pointMatrix_xcPoint, pointMatrix_xcPoint, mul_add,
    mul_one, add_mul, one_mul]
  have hS := pointMatrix_midPoint_of_not F (m := m) u
  rw [mul_eq_self_of_cols _ _ (fun l : Fin (m + K + 1) => m ≤ (l : ℕ) ∧ (l : ℕ) < m + K) hS
      (fun a l h => by have := xcMat_support_left _ _ a l h; omega)]
  congr 1
  ext a b
  rw [Matrix.mul_apply, sum_middle]
  · simp only [xcMat, rowMulRect, Matrix.mulVec, dotProduct]
    by_cases ha : m ≤ (a : ℕ) ∧ (a : ℕ) < m + K
    · rw [dite_eq_left ha]
      have hM : ∀ k : Fin K, pointMatrix F (midPoint F (m := m) u) a ⟨m + k, by omega⟩ =
          pointMatrix F u ⟨(a : ℕ) - m, by omega⟩ k := by
        intro k
        rw [pointMatrix_midPoint, dite_eq_left ⟨ha.1, ha.2, by simp, by simp⟩]
        simp
      simp_rw [hM]
      have hmk : ∀ k : Fin K, m ≤ ((⟨m + k, by omega⟩ : Fin (m + K + 1)) : ℕ) ∧
          ((⟨m + k, by omega⟩ : Fin (m + K + 1)) : ℕ) < m + K := fun k => ⟨by simp, by simp⟩
      simp only [dite_eq_left (hmk _)]
      by_cases hb : (b : ℕ) < m
      · rw [dite_eq_left hb]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [dite_eq_left hb]
        simp
      · rw [dite_eq_right hb]
        by_cases hb' : (b : ℕ) = m + K
        · rw [ite_eq_left hb']
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [dite_eq_right hb, ite_eq_left hb']
          simp
        · rw [ite_eq_right hb']
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [dite_eq_right hb, ite_eq_right hb', mul_zero]
    · rw [dite_eq_right ha]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hS a _ (Or.inl ha), Matrix.one_apply_ne (fun h => by
        have := congrArg Fin.val h; simp at this; omega), zero_mul]
  · intro l hl
    have : xcMat m K x c l b = 0 := by
      by_contra h
      exact hl (xcMat_support_right x c l b h)
    rw [this, mul_zero]

end MiddleAlgebra

section Padding

variable (F : Type u) [Field F] [NumberField F]
variable {m K : ℕ}

/-- The last row of a rectangle `x` on `K + 1` rows. -/
def rowOfRect (x : Fin (K + 1) × Fin m → Adeles F) : Fin m → Adeles F := fun j => x (Fin.last K, j)

/-- The first `K` rows of a rectangle `x` on `K + 1` rows. -/
def restOfRect (x : Fin (K + 1) × Fin m → Adeles F) : Fin K × Fin m → Adeles F :=
  fun p => x (p.1.castSucc, p.2)

theorem pointMatrix_xcPoint_mul_rowPoint (x : Fin K × Fin m → Adeles F) (b : Fin m → Adeles F) :
    pointMatrix F (xcPoint F x 0 * rowPoint F b) = 1 + xcMat m K x 0 + rowMat m K b := by
  rw [pointMatrix_mul, pointMatrix_xcPoint, pointMatrix_rowPoint, add_mul, one_mul, mul_add,
    mul_one, xcMat_mul_rowMat]
  have : outerRect (0 : Fin K → Adeles F) b = 0 := by funext p; simp [outerRect]
  rw [this, xcMat_zero, add_zero]
  abel

/-- A rectangular point on `K + 1` rows is the padding of a rectangular point on `K` rows times
a row point. -/
theorem xcPoint_succ_rect (x : Fin (K + 1) × Fin m → Adeles F) :
    xcPoint F (K := K + 1) x 0 =
      pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)
        (xcPoint F (restOfRect F x) 0 * rowPoint F (rowOfRect F x)) := by
  apply point_ext
  rw [pointMatrix_xcPoint]
  ext a b
  simp only [pointMatrix, adelicEquiv_pad]
  rw [padGL_apply]
  have key := pointMatrix_xcPoint_mul_rowPoint F (restOfRect F x) (rowOfRect F x)
  simp only [pointMatrix] at key
  simp only [key, Matrix.add_apply, xcMat, rowMat, restOfRect, rowOfRect, Pi.zero_apply,
    Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first
    | omega
    | rfl
    | (simp only [zero_add, add_zero]; done)
    | (simp only [zero_add, add_zero, Fin.castSucc_mk]; done)
    | (simp only [zero_add, add_zero]; congr 2; ext; simp; omega)

end Padding

section MorePadding

variable (F : Type u) [Field F] [NumberField F]
variable {m K : ℕ}

/-- A column vector on the rows `m, …, m+K` of `GL_(m+K+2)`. -/
def extCol (c : Fin (K + 1) → Adeles F) : Fin (m + (K + 1) + 1) → Adeles F := fun a =>
  if h : m ≤ (a : ℕ) ∧ (a : ℕ) < m + (K + 1) then c ⟨(a : ℕ) - m, by omega⟩ else 0

theorem isColSupported_extCol (c : Fin (K + 1) → Adeles F) :
    IsColSupported (m + K) (extCol F (m := m) c) := by
  intro a ha
  simp only [extCol]
  rw [dite_eq_right (by omega)]

/-- A pure column point on `K + 1` rows is the column point of `GL_(m+K+2)` in the last
column. -/
theorem pointMatrix_xcPoint_col (c : Fin (K + 1) → Adeles F) :
    pointMatrix F (xcPoint F (m := m) (K := K + 1) 0 c) = 1 + colMatrix (m + K) (extCol F c) := by
  rw [pointMatrix_xcPoint]
  ext a b
  simp only [Matrix.add_apply, xcMat, colMatrix_apply, extCol, Pi.zero_apply]
  split_ifs <;> first | omega | rfl

/-- The last-column matrix of `GL_(K+1)`. -/
def lastColMat {R : Type*} [CommRing R] (c : Fin K → R) : Matrix (Fin (K + 1)) (Fin (K + 1)) R :=
  fun a b => if h : (a : ℕ) < K ∧ (b : ℕ) = K then c ⟨a, h.1⟩ else 0

theorem lastColMat_mul {R : Type*} [CommRing R] (c d : Fin K → R) :
    lastColMat c * lastColMat d = 0 :=
  mul_eq_zero_of_support _ _ (fun l : Fin (K + 1) => (l : ℕ) = K)
    (fun l : Fin (K + 1) => (l : ℕ) < K)
    (fun a l h => by simp only [lastColMat] at h; split_ifs at h with h1; exact h1.2; exact absurd rfl h)
    (fun l b h => by simp only [lastColMat] at h; split_ifs at h with h1; exact h1.1; exact absurd rfl h)
    (fun l h1 h2 => by omega)

/-- The last-column point of `GL_(K+1)(𝔸)`. -/
def lastColPoint (c : Fin K → Adeles F) : Points F (K + 1) :=
  (GeneralLinearGroupPoints.adelicEquiv F (K + 1)).symm (sqZeroUnit (lastColMat c) (lastColMat_mul c c))

theorem pointMatrix_lastColPoint (c : Fin K → Adeles F) :
    pointMatrix F (lastColPoint F c) = 1 + lastColMat c := by
  simp only [pointMatrix, lastColPoint, MulEquiv.apply_symm_apply, sqZeroUnit_val]

theorem midPoint_mul (u v : Points F K) :
    midPoint F (m := m) (u * v) = midPoint F u * midPoint F v := by
  simp only [midPoint, map_mul, pad_mul]

theorem midPoint_one : midPoint F (m := m) (1 : Points F K) = 1 := by
  simp only [midPoint, map_one]
  apply point_ext
  ext a b
  simp only [pointMatrix, adelicEquiv_pad, map_one]

/-- The middle-block image of a last-column point is a padded column point. -/
theorem midPoint_lastColPoint (c : Fin K → Adeles F) :
    midPoint F (m := m) (K := K + 1) (lastColPoint F c) =
      pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) (xcPoint F 0 c) := by
  apply point_ext
  ext a b
  rw [pointMatrix_midPoint, pointMatrix_lastColPoint]
  simp only [pointMatrix, adelicEquiv_pad]
  rw [padGL_apply]
  change _ = if hi : (a : ℕ) < m + K + 1 then
      (if hj : (b : ℕ) < m + K + 1 then pointMatrix F (xcPoint F (m := m) (K := K) 0 c) ⟨a, hi⟩ ⟨b, hj⟩
        else 0) else (if a = b then 1 else 0)
  rw [pointMatrix_xcPoint]
  simp only [Matrix.add_apply, xcMat, lastColMat, Matrix.one_apply, Fin.ext_iff, Pi.zero_apply]
  split_ifs <;> first | omega | rfl | simp only [add_zero]

/-- The middle-block image of a padded point is the padded middle-block image. -/
theorem midPoint_pad (u : Points F K) :
    midPoint F (m := m) (K := K + 1) (pad F (Nat.le_succ K) u) =
      pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) (midPoint F u) := by
  apply point_ext
  ext a b
  rw [pointMatrix_midPoint]
  simp only [pointMatrix, adelicEquiv_pad]
  simp only [padGL_apply]
  change _ = if hi : (a : ℕ) < m + K + 1 then
      (if hj : (b : ℕ) < m + K + 1 then pointMatrix F (midPoint F (m := m) u) ⟨a, hi⟩ ⟨b, hj⟩
        else 0) else (if a = b then 1 else 0)
  simp only [pointMatrix_midPoint, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

end MorePadding

section SuperSum

variable (F : Type u) [Field F] [NumberField F]
variable {K : ℕ}

/-- The sum of the superdiagonal entries of a point of `GL_K(𝔸)`. -/
def superSum (u : Points F K) : Adeles F :=
  ∑ i : Fin K, if h : (i : ℕ) + 1 < K then pointMatrix F u i ⟨(i : ℕ) + 1, h⟩ else 0

/-- The last entry of a vector, and `0` for the empty vector. -/
def lastEntry {R : Type*} [AddCommMonoid R] (c : Fin K → R) : R :=
  ∑ i : Fin K, if (i : ℕ) + 1 = K then c i else 0

theorem superSum_lastColPoint_mul_pad (c : Fin K → Adeles F) (u : Points F K) :
    superSum F (lastColPoint F c * pad F (Nat.le_succ K) u) = lastEntry c + superSum F u := by
  unfold superSum lastEntry
  rw [Fin.sum_univ_castSucc, dite_eq_right (by simp), add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dite_eq_left (by simp)]
  rw [pointMatrix_mul, pointMatrix_lastColPoint, add_mul, one_mul, Matrix.add_apply,
    Matrix.mul_apply, Finset.sum_eq_single (Fin.last K)]
  · simp only [pointMatrix, adelicEquiv_pad, padGL_apply, lastColMat, Fin.val_castSucc,
      Fin.val_last, Fin.ext_iff, and_true]
    split_ifs <;> first | (exfalso; omega) | (simp; done)
  · intro l _ hl
    simp only [lastColMat]
    rw [dite_eq_right (fun h => hl (Fin.ext (by simp; omega))), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem superSum_mul (u v : Points F K)
    (hu : PrimitiveAdelicHeight.IsUnitriangular (pointMatrix F u))
    (hv : PrimitiveAdelicHeight.IsUnitriangular (pointMatrix F v)) :
    superSum F (u * v) = superSum F u + superSum F v := by
  unfold superSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (i : ℕ) + 1 < K
  · rw [dite_eq_left hi, dite_eq_left hi, dite_eq_left hi, pointMatrix_mul, Matrix.mul_apply]
    rw [Fintype.sum_eq_add i ⟨(i : ℕ) + 1, hi⟩ (fun h => by
      have := congrArg Fin.val h; simp at this)]
    · rw [hu.2 i, hv.2, one_mul, mul_one, add_comm]
    · intro l hl
      by_cases hli : (l : ℕ) < i
      · rw [hu.1 (show l < i from hli), zero_mul]
      · have hl2 : (⟨(i : ℕ) + 1, hi⟩ : Fin K) < l := by
          show (i : ℕ) + 1 < l
          have h1 : (l : ℕ) ≠ i := fun h => hl.1 (Fin.ext h)
          have h2 : (l : ℕ) ≠ (i : ℕ) + 1 := fun h => hl.2 (Fin.ext (by simpa using h))
          omega
        rw [hv.1 hl2, mul_zero]
  · rw [dite_eq_right hi, dite_eq_right hi, dite_eq_right hi, add_zero]

end SuperSum

end Langlands.Global.RankinSelbergGlobal.Unfolding

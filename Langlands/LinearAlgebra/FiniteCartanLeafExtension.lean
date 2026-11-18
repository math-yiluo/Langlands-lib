import Langlands.LinearAlgebra.FiniteCartanDiagram
import Langlands.LinearAlgebra.FiniteCartanClassificationStatement

/-! # Positivity restrictions for adding a leaf -/

open Matrix Finset

namespace Langlands.LinearAlgebra.FiniteCartanMatrix

/-- Append a vertex linked only to `k`, with the two ordered entries `a,b`. -/
def leafExtension {n : ℕ} (N : Matrix (Fin n) (Fin n) ℤ)
    (k : Fin n) (a b : ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => Fin.lastCases
    (Fin.lastCases 2 (fun j => if j = k then b else 0) j)
    (fun i => Fin.lastCases (if i = k then a else 0) (fun j => N i j) j) i

@[simp] theorem leafExtension_castSucc_castSucc {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (k i j : Fin n) (a b : ℤ) :
    leafExtension N k a b i.castSucc j.castSucc = N i j := by
  simp [leafExtension]

@[simp] theorem leafExtension_castSucc_last {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (k i : Fin n) (a b : ℤ) :
    leafExtension N k a b i.castSucc (Fin.last n) = if i = k then a else 0 := by
  simp [leafExtension]

@[simp] theorem leafExtension_last_castSucc {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (a b : ℤ) :
    leafExtension N k a b (Fin.last n) j.castSucc = if j = k then b else 0 := by
  simp [leafExtension]

@[simp] theorem leafExtension_last_last {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) (a b : ℤ) :
    leafExtension N k a b (Fin.last n) (Fin.last n) = 2 := by
  simp [leafExtension]

theorem leafExtension_mulVec_castSucc {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (k i : Fin n) (a b c : ℤ) (y : Fin n → ℤ) :
    (leafExtension N k a b *ᵥ Fin.lastCases c y) i.castSucc =
      (N *ᵥ y) i + (if i = k then a * c else 0) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
    leafExtension_castSucc_castSucc, Fin.lastCases_castSucc,
    leafExtension_castSucc_last, Fin.lastCases_last]
  split_ifs <;> simp

theorem leafExtension_mulVec_last {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) (a b c : ℤ) (y : Fin n → ℤ) :
    (leafExtension N k a b *ᵥ Fin.lastCases c y) (Fin.last n) =
      b * y k + 2 * c := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, ite_mul]

theorem leafExtension_positive_bound {n : ℕ}
    {N : Matrix (Fin n) (Fin n) ℤ} {k : Fin n} {a b c : ℤ} {y : Fin n → ℤ}
    (hE : (leafExtension N k a b).IsFiniteCartan)
    (ha : a ≤ 0) (hc : 0 < c) (hy0 : ∀ j, 0 ≤ y j)
    (hy : N *ᵥ y = fun j => if j = k then c else 0) :
    0 < 2 * c - a * b * y k := by
  let x : Fin (n + 1) → ℤ := Fin.lastCases c ((-a) • y)
  have hx0 : x ≠ 0 := by
    intro h
    have heq := congr_fun h (Fin.last n)
    simp only [x, Fin.lastCases_last, Pi.zero_apply] at heq
    omega
  have hx : ∀ j, 0 ≤ x j := by
    intro j
    refine Fin.lastCases (motive := fun j => 0 ≤ x j) ?_ ?_ j
    · simpa [x] using hc.le
    · intro j
      simpa [x] using mul_nonneg (neg_nonneg.mpr ha) (hy0 j)
  have hcast (j : Fin n) :
      (leafExtension N k a b *ᵥ x) j.castSucc = 0 := by
    rw [show x = Fin.lastCases c ((-a) • y) from rfl,
      leafExtension_mulVec_castSucc, Matrix.mulVec_smul, hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  have hlast : (leafExtension N k a b *ᵥ x) (Fin.last n) =
      2 * c - a * b * y k := by
    rw [show x = Fin.lastCases c ((-a) • y) from rfl, leafExtension_mulVec_last]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨i, _, hi⟩ := exists_positive_mulVec hE x hx hx0
  exact Fin.lastCases
    (motive := fun i => 0 < (leafExtension N k a b *ᵥ x) i →
      0 < 2 * c - a * b * y k)
    (by simp [hlast])
    (fun j h => by simp [hcast j] at h) i hi

theorem leafExtension_negative_pairs {n : ℕ}
    {N : Matrix (Fin n) (Fin n) ℤ} {k : Fin n} {a b : ℤ}
    (hE : (leafExtension N k a b).IsFiniteCartan) (ha : a < 0) :
    (a = -1 ∧ b = -1) ∨ (a = -1 ∧ b = -2) ∨
    (a = -2 ∧ b = -1) ∨ (a = -1 ∧ b = -3) ∨
    (a = -3 ∧ b = -1) := by
  have hp := ordered_entries hE k.castSucc (Fin.last n) k.castSucc_ne_last
  simpa only [leafExtension_castSucc_last, leafExtension_last_castSucc,
    ite_true, ha.ne, false_and, false_or] using hp

theorem leafExtension_columnMatrix_bound {n : ℕ}
    {N K : Matrix (Fin n) (Fin n) ℤ} {k : Fin n} {a b c : ℤ}
    (hE : (leafExtension N k a b).IsFiniteCartan) (ha : a ≤ 0)
    (hc : 0 < c) (hK0 : ∀ i j, 0 ≤ K i j) (hK : N * K = c • 1) :
    a * b * K k k < 2 * c := by
  have hy : N *ᵥ (fun i => K i k) = fun i => if i = k then c else 0 := by
    ext i
    have he := congr_fun (congr_fun hK i) k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, mul_ite] using he
  have hp := leafExtension_positive_bound hE ha hc (fun i => hK0 i k) hy
  omega

end Langlands.LinearAlgebra.FiniteCartanMatrix

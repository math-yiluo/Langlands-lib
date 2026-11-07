import Langlands.Representation.RankinSelberg.SymmetricPieri

/-! # Dominance, shifts and the Jacobi–Trudi Pieri rule -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The Jacobi–Trudi polynomial on dominant weights, and zero elsewhere. -/
def dominantJacobiTrudi (R : Type*) [CommRing R] {m : ℕ} (α : Fin m → ℤ) :
    MvPolynomial (Fin m) R :=
  if Antitone α then jacobiTrudi R α else 0

/-- A raise that breaks dominance creates two equal adjacent Jacobi–Trudi rows. -/
theorem jacobiTrudi_raiseWeight_eq_zero {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : Antitone α) (s : Finset (Fin (n + 1)))
    (hs : ¬ Antitone (raiseWeight α s)) :
    jacobiTrudi R (raiseWeight α s) = 0 := by
  have hbad : ∃ i : Fin n, raiseWeight α s i.castSucc < raiseWeight α s i.succ := by
    simpa only [Fin.antitone_iff_succ_le, not_forall, not_le] using hs
  obtain ⟨i, hi⟩ := hbad
  have hbase := hα (show i.castSucc ≤ i.succ by exact Fin.castSucc_le_succ i)
  have hrow : raiseWeight α s i.castSucc - (i.castSucc : ℤ) =
      raiseWeight α s i.succ - (i.succ : ℤ) := by
    simp only [raiseWeight] at hi ⊢
    by_cases h₁ : i.castSucc ∈ s <;> by_cases h₂ : i.succ ∈ s <;>
      simp only [h₁, h₂, ite_true, ite_false, Fin.val_castSucc, Fin.val_succ,
        Nat.cast_add, Nat.cast_one] at hi ⊢ <;> omega
  unfold jacobiTrudi
  apply Matrix.det_zero_of_row_eq
    (show i.castSucc ≠ i.succ from fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega)
  funext j
  simp only [Matrix.of_apply, hrow]

/-- Multiplication by a common variable power implements a uniform weight shift. -/
theorem alternantMatrix_add_nat {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : ∀ i, 0 ≤ α i) (c : ℕ) :
    alternantMatrix R (fun i => α i + c) =
      alternantMatrix R α * Matrix.diagonal (fun j => (X j) ^ c) := by
  apply Matrix.ext
  intro i j
  have he : (α i + c - i + n).toNat = (α i - i + n).toNat + c := by
    have := hα i
    have := i.isLt
    omega
  simp [alternantMatrix, Matrix.mul_diagonal, he, pow_add]

/-- Uniform nonnegative shifts multiply Jacobi–Trudi by the determinant monomial. -/
theorem jacobiTrudi_add_nat [IsDomain R] {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : ∀ i, 0 ≤ α i) (c : ℕ) :
    jacobiTrudi R (fun i => α i + c) =
      jacobiTrudi R α * (∏ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) R)) ^ c := by
  have hD : Matrix.det (alternantMatrix R (0 : Fin (n + 1) → ℤ)) ≠ 0 := by
    rw [← det_erasedCoefficientMatrix]
    exact det_erasedCoefficientMatrix_ne_zero n
  apply mul_right_cancel₀ hD
  rw [jacobiTrudi_mul_baseAlternant _ (fun i => by have := hα i; omega),
    alternantMatrix_add_nat α hα, Matrix.det_mul, Matrix.det_diagonal,
    ← Finset.prod_pow, ← jacobiTrudi_mul_baseAlternant α hα]
  ring

/-- On a partition, the elementary Pieri sum can omit all nondominant raises. -/
theorem dominantJacobiTrudi_mul_esymm [IsDomain R] {n : ℕ}
    (α : Fin (n + 1) → ℤ) (hα : Antitone α) (hpos : ∀ i, 0 ≤ α i) (k : ℕ) :
    dominantJacobiTrudi R α * esymm (Fin (n + 1)) R k =
      ∑ s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard k,
        dominantJacobiTrudi R (raiseWeight α s) := by
  rw [dominantJacobiTrudi, ite_eq_left hα, jacobiTrudi_mul_esymm α hpos]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Antitone (raiseWeight α s)
  · rw [dominantJacobiTrudi, ite_eq_left hs]
  · rw [dominantJacobiTrudi, ite_eq_right hs, jacobiTrudi_raiseWeight_eq_zero α hα s hs]

/-- Nonnegative dominant weights have the ordinary polynomial Schur evaluation. -/
theorem satakeSchur_eq_eval_jacobiTrudi {n : ℕ} (x : Fin (n + 1) → ℂˣ)
    (α : Fin (n + 1) → ℤ) (hα : Antitone α) (hpos : ∀ i, 0 ≤ α i) :
    satakeSchur x α = eval (fun i => (x i : ℂ)) (jacobiTrudi ℂ α) := by
  have hshift := jacobiTrudi_add_nat (R := ℂ)
    (fun i => α i - α (Fin.last n))
    (fun i => sub_nonneg.mpr (hα (Fin.le_last i))) (α (Fin.last n)).toNat
  have he : (fun i => α i - α (Fin.last n) + ((α (Fin.last n)).toNat : ℤ)) = α := by
    funext i
    rw [Int.toNat_of_nonneg (hpos _)]
    omega
  rw [he] at hshift
  rw [satakeSchur, hshift, map_mul, map_pow, map_prod]
  simp only [eval_X]
  rw [← zpow_natCast, Int.toNat_of_nonneg (hpos _)]
  exact mul_comm _ _

end Langlands.GeneralLinear.Spherical

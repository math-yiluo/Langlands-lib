import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.MatrixAlgebra

/-! # Upper triangular factorization over a division ring -/

namespace Langlands.GeneralLinearGroup

open Matrix

universe u

variable {D : Type u} [DivisionRing D] (O : Subring D)

private abbrev integralMatrixUnits (n : ℕ) : Subgroup (Matrix (Fin n) (Fin n) D)ˣ :=
  (O.matrix (n := Fin n)).toSubmonoid.units

private theorem mem_integral_matrixUnits {n : ℕ} (g : (Matrix (Fin n) (Fin n) D)ˣ) :
    g ∈ integralMatrixUnits O n ↔ (∀ i j, g.val i j ∈ O) ∧ (∀ i j, g.inv i j ∈ O) :=
  Iff.rfl

private theorem exists_last_dominant_division (v : AbsoluteValue D ℝ) {n : ℕ}
    (g : (Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ) :
    ∃ k ∈ integralMatrixUnits O (n + 1), (g * k).val (Fin.last n) (Fin.last n) ≠ 0 ∧
      ∀ j, v ((g * k).val (Fin.last n) j) ≤ v ((g * k).val (Fin.last n) (Fin.last n)) := by
  classical
  let i := Fin.last n
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => v (g.val i j))
    Finset.univ_nonempty
  have hj : g.val i j ≠ 0 := by
    intro hzero
    have hrow (l : Fin (n + 1)) : g.val i l = 0 := by
      have hl := hmax l (Finset.mem_univ l)
      rw [hzero, map_zero] at hl
      exact v.eq_zero.mp (le_antisymm hl (v.nonneg _))
    have h := congrArg (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) D => x i i) g.val_inv
    simp [Matrix.mul_apply, hrow] at h
  let σ := Equiv.swap j i
  let k : (Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ :=
    ⟨σ.permMatrix D, (σ⁻¹).permMatrix D,
      by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
      by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩
  have hk : k ∈ integralMatrixUnits O (n + 1) := by
    apply (mem_integral_matrixUnits O k).mpr
    have hperm (p : Equiv.Perm (Fin (n + 1))) (a b : Fin (n + 1)) : p.permMatrix D a b ∈ O := by
      change (p.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) D) a b ∈ O
      rw [PEquiv.toMatrix_apply]
      split_ifs <;> simp
    exact ⟨hperm σ, hperm σ⁻¹⟩
  have hentry (l : Fin (n + 1)) : (g * k).val i l = g.val i (σ.symm l) := by
    change (g.val * (σ.permMatrix D)) i l = _
    rw [PEquiv.mul_toMatrix_toPEquiv]
    rfl
  have hpivot : (g * k).val i i = g.val i j := by
    rw [hentry]
    simp [σ]
  exact ⟨k, hk, fun h => hj (hpivot.symm.trans h),
    fun l => by rw [hentry, hpivot]; exact hmax _ (Finset.mem_univ _)⟩

private def divisionLastRow {n : ℕ} (c : Fin (n + 1) → D) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) D :=
  Matrix.of fun i j => if i = Fin.last n ∧ j ≠ Fin.last n then c j else 0

private theorem clear_last_row_division (v : AbsoluteValue D ℝ)
    (hO : ∀ a : D, a ∈ O ↔ v a ≤ 1) {n : ℕ}
    (g : (Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ)
    (hg : g.val (Fin.last n) (Fin.last n) ≠ 0)
    (hdom : ∀ j, v (g.val (Fin.last n) j) ≤ v (g.val (Fin.last n) (Fin.last n))) :
    ∃ k ∈ integralMatrixUnits O (n + 1),
      (∀ j, j ≠ Fin.last n → (g * k).val (Fin.last n) j = 0) ∧
      (g * k).val (Fin.last n) (Fin.last n) = g.val (Fin.last n) (Fin.last n) := by
  let i := Fin.last n
  let a := g.val i i
  let c (j : Fin (n + 1)) := a⁻¹ * g.val i j
  let N := divisionLastRow c
  have hNN : N * N = 0 := by
    ext l j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro b _
    simp only [N, divisionLastRow, Matrix.of_apply]
    split_ifs <;> simp_all
  let k : (Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ :=
    ⟨1 - N, 1 + N,
      by rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hNN]; abel,
      by rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hNN]; abel⟩
  have hc (j : Fin (n + 1)) : c j ∈ O := by
    rw [hO]
    change v (a⁻¹ * g.val i j) ≤ 1
    rw [map_mul, IsAbsoluteValue.abv_inv (⇑v) a]
    calc
      (v a)⁻¹ * v (g.val i j) ≤ (v a)⁻¹ * v a :=
        mul_le_mul_of_nonneg_left (hdom j) (inv_nonneg.mpr (v.nonneg a))
      _ = 1 := inv_mul_cancel₀ (v.ne_zero hg)
  have hN (l j : Fin (n + 1)) : N l j ∈ O := by
    change (if l = Fin.last n ∧ j ≠ Fin.last n then c j else 0) ∈ O
    split_ifs with h
    · exact hc j
    · exact O.zero_mem
  have hone (l j : Fin (n + 1)) : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) D) l j ∈ O := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hk : k ∈ integralMatrixUnits O (n + 1) :=
    (mem_integral_matrixUnits O k).mpr
      ⟨fun l j => O.sub_mem (hone l j) (hN l j), fun l j => O.add_mem (hone l j) (hN l j)⟩
  have hentry (j : Fin (n + 1)) : (g * k).val i j = g.val i j - a * N i j := by
    change (g.val * (1 - N)) i j = _
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_apply,
      Finset.sum_eq_single i]
    · intro l _ hl
      simp [N, divisionLastRow, show l ≠ Fin.last n from hl]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨k, hk, fun j hj => ?_, ?_⟩
  · rw [hentry]
    change g.val i j - a * (if i = Fin.last n ∧ j ≠ Fin.last n then c j else 0) = 0
    rw [ite_eq_left ⟨rfl, hj⟩]
    change g.val i j - a * (a⁻¹ * g.val i j) = 0
    rw [mul_inv_cancel_left₀ hg, sub_self]
  · rw [hentry]
    simp [i, N, divisionLastRow]

private def lastBlockOne {n : ℕ} (a : Matrix (Fin n) (Fin n) D) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) D :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
    (fun i => Fin.lastCases 0 (a i) j) i

@[simp]
private theorem lastBlockOne_castSucc_castSucc {n : ℕ} (a : Matrix (Fin n) (Fin n) D)
    (i j : Fin n) : lastBlockOne a i.castSucc j.castSucc = a i j := by
  simp [lastBlockOne]

@[simp]
private theorem lastBlockOne_last_castSucc {n : ℕ} (a : Matrix (Fin n) (Fin n) D) (j : Fin n) :
    lastBlockOne a (Fin.last n) j.castSucc = 0 := by simp [lastBlockOne]

@[simp]
private theorem lastBlockOne_castSucc_last {n : ℕ} (a : Matrix (Fin n) (Fin n) D) (i : Fin n) :
    lastBlockOne a i.castSucc (Fin.last n) = 0 := by simp [lastBlockOne]

@[simp]
private theorem lastBlockOne_last_last {n : ℕ} (a : Matrix (Fin n) (Fin n) D) :
    lastBlockOne a (Fin.last n) (Fin.last n) = 1 := by simp [lastBlockOne]

private def lastBlockOneHom (n : ℕ) : Matrix (Fin n) (Fin n) D →*
    Matrix (Fin (n + 1)) (Fin (n + 1)) D where
  toFun := lastBlockOne
  map_one' := by
    ext i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [Matrix.one_apply, (Fin.castSucc_ne_last _).symm]
  map_mul' a b := by
    ext i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

private def truncateDivisionUnit {n : ℕ} (g : (Matrix (Fin (n + 1)) (Fin (n + 1)) D)ˣ)
    (hrow : ∀ j : Fin n, g.val (Fin.last n) j.castSucc = 0)
    (hdiag : g.val (Fin.last n) (Fin.last n) ≠ 0) :
    (Matrix (Fin n) (Fin n) D)ˣ := by
  have hInvRow (j : Fin n) : g.inv (Fin.last n) j.castSucc = 0 := by
    have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) D => A (Fin.last n) j.castSucc)
      g.val_inv
    change (g.val * g.inv) (Fin.last n) j.castSucc = _ at h
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc] at h
    simp only [hrow, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply,
      (Fin.castSucc_ne_last j).symm, ite_false] at h
    exact (mul_eq_zero.mp h).resolve_left hdiag
  refine ⟨g.val.submatrix Fin.castSucc Fin.castSucc, g.inv.submatrix Fin.castSucc Fin.castSucc,
    ?_, ?_⟩
  · ext i j
    have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) D => A i.castSucc j.castSucc)
      g.val_inv
    change (g.val * g.inv) i.castSucc j.castSucc = _ at h
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hInvRow, mul_zero, add_zero] at h
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Fin.castSucc_inj] using h
  · ext i j
    have h := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) D => A i.castSucc j.castSucc)
      g.inv_val
    change (g.inv * g.val) i.castSucc j.castSucc = _ at h
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hrow, mul_zero, add_zero] at h
    simpa only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Fin.castSucc_inj] using h

/-- A multiplicative absolute value with unit ball `O` allows integral column operations
to put any invertible matrix over a division ring in upper triangular form. -/
def DivisionMatrixIwasawaStatement (v : AbsoluteValue D ℝ) : Prop :=
  (∀ a : D, a ∈ O ↔ v a ≤ 1) →
    ∀ (n : ℕ) (g : (Matrix (Fin n) (Fin n) D)ˣ),
      ∃ k ∈ integralMatrixUnits O n, (g * k).val.IsUpperTriangular

theorem divisionMatrixIwasawa (v : AbsoluteValue D ℝ) : DivisionMatrixIwasawaStatement O v := by
  intro hO n
  induction n with
  | zero =>
    intro g
    exact ⟨1, one_mem _, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro g
    obtain ⟨k₁, hk₁, hne, hdom⟩ := exists_last_dominant_division O v g
    obtain ⟨k₂, hk₂, hrow, hlast⟩ := clear_last_row_division O v hO (g * k₁) hne hdom
    let g' := g * k₁ * k₂
    have hrow' (j : Fin n) : g'.val (Fin.last n) j.castSucc = 0 :=
      hrow j.castSucc (Fin.castSucc_ne_last j)
    let a := truncateDivisionUnit g' hrow' (fun h => hne (hlast.symm.trans h))
    obtain ⟨k₃, hk₃, hup⟩ := ih a
    let k := Units.map (lastBlockOneHom n) k₃
    have hk : k ∈ integralMatrixUnits O (n + 1) := by
      obtain ⟨hv, hi⟩ := (mem_integral_matrixUnits O k₃).mp hk₃
      have hi' (i j : Fin n) : k₃⁻¹.val i j ∈ O := hi i j
      refine (mem_integral_matrixUnits O k).mpr ⟨?_, ?_⟩
      · intro i j
        change lastBlockOne k₃.val i j ∈ O
        induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [hv]
      · intro i j
        change lastBlockOne k₃.inv i j ∈ O
        induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [hi']
    refine ⟨k₁ * k₂ * k, mul_mem (mul_mem hk₁ hk₂) hk, ?_⟩
    have he : g * (k₁ * k₂ * k) = g' * k := by simp only [g', mul_assoc]
    rw [he]
    intro i j hji
    induction j using Fin.lastCases with
    | last => exact (not_lt.mpr (Fin.le_last i) hji).elim
    | cast j =>
      change (g'.val * lastBlockOne k₃.val) i j.castSucc = 0
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      simp only [lastBlockOne_castSucc_castSucc, lastBlockOne_last_castSucc, mul_zero, add_zero]
      induction i using Fin.lastCases with
      | last => simp only [hrow', zero_mul, Finset.sum_const_zero]
      | cast i =>
        have h : j < i := Fin.castSucc_lt_castSucc_iff.mp hji
        exact hup h

end Langlands.GeneralLinearGroup

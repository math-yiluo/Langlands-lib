import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial

/-! # A polynomial weight on `O(n)` with block-diagonal maximum level -/

noncomputable section

open Matrix Set

set_option autoImplicit false

namespace Langlands.Archimedean

open OrthogonalFinitePolynomial

private abbrev O (n : ℕ) := Matrix.unitaryGroup (Fin n) ℝ

variable {n : ℕ}

private def conjugationDifference (d : Fin n → ℝ) (k : O n) :
    Matrix (Fin n) (Fin n) ℝ :=
  k.valᵀ * diagonal d * k.val - diagonal d

private theorem conjugationDifference_apply (d : Fin n → ℝ) (k : O n) (i j : Fin n) :
    conjugationDifference d k i j =
      (∑ r, k.val r i * d r * k.val r j) - diagonal d i j := by
  unfold conjugationDifference
  rw [Matrix.sub_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

private theorem transpose_mul_self (k : O n) : k.valᵀ * k.val = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp k.2
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

private theorem blockDiagonal_iff_commute (d : Fin n → ℝ) (k : O n) :
    (∀ i j, d i ≠ d j → k.val i j = 0) ↔ diagonal d * k.val = k.val * diagonal d := by
  constructor
  · intro hk
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · rw [hk i j hij, mul_zero, zero_mul]
  · intro hk i j hij
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hk
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hzero : (d i - d j) * k.val i j = 0 := by
      rw [sub_mul, he, mul_comm (d j), sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hij)

private theorem conjugationDifference_eq_zero_iff (d : Fin n → ℝ) (k : O n) :
    conjugationDifference d k = 0 ↔ ∀ i j, d i ≠ d j → k.val i j = 0 := by
  have hkk := mul_eq_one_comm.mp (transpose_mul_self k)
  rw [blockDiagonal_iff_commute, conjugationDifference, sub_eq_zero]
  constructor
  · intro h
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => k.val * A) h
    change k.val * (k.valᵀ * diagonal d * k.val) = _ at he
    rwa [← Matrix.mul_assoc k.val, ← Matrix.mul_assoc k.val, hkk, Matrix.one_mul] at he
  · intro h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, transpose_mul_self k, Matrix.one_mul]

private theorem conjugationDifference_mul (d : Fin n → ℝ) {h : O n}
    (hh : ∀ i j, d i ≠ d j → h.val i j = 0) (k : O n) :
    conjugationDifference d (h * k) = conjugationDifference d k := by
  have he := (conjugationDifference_eq_zero_iff d h).2 hh
  rw [conjugationDifference, sub_eq_zero] at he
  change (h.val * k.val)ᵀ * diagonal d * (h.val * k.val) - diagonal d =
    k.valᵀ * diagonal d * k.val - diagonal d
  rw [Matrix.transpose_mul]
  congr 1
  calc
    k.valᵀ * h.valᵀ * diagonal d * (h.val * k.val) =
        k.valᵀ * (h.valᵀ * diagonal d * h.val) * k.val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [he]

private def energy (d : Fin n → ℝ) (k : O n) : ℝ :=
  ∑ i, ∑ j, (conjugationDifference d k i j) ^ 2

private theorem energy_nonneg (d : Fin n → ℝ) (k : O n) : 0 ≤ energy d k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem energy_zero_iff (d : Fin n → ℝ) (k : O n) :
    energy d k = 0 ↔ conjugationDifference d k = 0 := by
  constructor
  · intro h
    ext i j
    rw [Matrix.zero_apply]
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (conjugationDifference d k i j))).mp
        h i (Finset.mem_univ i)
    have hentry := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (conjugationDifference d k i j))).mp hrow j (Finset.mem_univ j)
    exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hentry
  · intro h
    simp [energy, h]

private theorem continuous_energy (d : Fin n → ℝ) : Continuous (energy d) := by
  have hk : Continuous (Subtype.val : O n → Matrix (Fin n) (Fin n) ℝ) :=
    continuous_subtype_val
  have hd : Continuous (conjugationDifference d) :=
    ((hk.matrix_transpose.matrix_mul continuous_const).matrix_mul hk).sub continuous_const
  exact continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (hd.matrix_elem i j).pow 2

private theorem energy_mem_polynomialFunctions (d : Fin n → ℝ) :
    (fun k => (energy d k : ℂ)) ∈ polynomialFunctions n := by
  let P := polynomialFunctions n
  have hentry (i j : Fin n) :
      (fun k => (conjugationDifference d k i j : ℂ)) ∈ P := by
    have h := P.sub_mem (P.sum_mem fun r (_ : r ∈ Finset.univ) =>
      P.mul_mem
        (P.mul_mem (entry_mem_polynomialFunctions (r, i)) (P.algebraMap_mem (d r : ℂ)))
        (entry_mem_polynomialFunctions (r, j))) (P.algebraMap_mem ((diagonal d i j : ℝ) : ℂ))
    convert h using 1
    funext k
    simp only [conjugationDifference_apply, Complex.ofReal_sub, Complex.ofReal_sum,
      Complex.ofReal_mul, Pi.sub_apply, Finset.sum_apply, Pi.mul_apply,
      entry_apply, Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
  have h := P.sum_mem fun i (_ : i ∈ Finset.univ) =>
    P.sum_mem fun j (_ : j ∈ Finset.univ) => P.pow_mem (hentry i j) 2
  convert h using 1
  funext k
  simp only [energy, Complex.ofReal_sum, Complex.ofReal_pow, Finset.sum_apply, Pi.pow_apply]

/-- A real polynomial weight on `O(n)` lies in `[0, 1]`, is invariant under left
multiplication by block-diagonal elements, and is 1 exactly on those elements.
Equal values of `d` specify the coordinate blocks. -/
def OrthogonalBlockPeakStatement : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ),
    ∃ p : Matrix.unitaryGroup (Fin n) ℝ → ℝ,
      Continuous p ∧ (fun k => (p k : ℂ)) ∈ polynomialFunctions n ∧
      (∀ k, p k ∈ Icc 0 1) ∧
      (∀ k, p k = 1 ↔ ∀ i j, d i ≠ d j → k.val i j = 0) ∧
      ∀ h, (∀ i j, d i ≠ d j → h.val i j = 0) → ∀ k, p (h * k) = p k

theorem orthogonalBlockPeak : OrthogonalBlockPeakStatement := by
  intro n d
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_energy d).continuousOn
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM (1 : O n) (mem_univ _))
  let C := M + 1
  have hC : 0 < C := by dsimp [C]; linarith
  let p : O n → ℝ := fun k => 1 - energy d k / C
  refine ⟨p, continuous_const.sub ((continuous_energy d).div_const C), ?_, ?_, ?_, ?_⟩
  · let P := polynomialFunctions n
    simp only [p, div_eq_mul_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul]
    exact P.sub_mem P.one_mem
      (P.mul_mem (energy_mem_polynomialFunctions d) (P.algebraMap_mem (C⁻¹ : ℝ)))
  · intro k
    have hn := energy_nonneg d k
    have hb : energy d k ≤ M := by
      simpa only [Real.norm_of_nonneg hn] using hM k (mem_univ k)
    have hle : energy d k / C ≤ 1 := (div_le_one hC).2 (by dsimp [C]; linarith)
    exact ⟨sub_nonneg.mpr hle, sub_le_self _ (div_nonneg hn hC.le)⟩
  · intro k
    have hp : p k = 1 ↔ energy d k = 0 := by
      dsimp only [p]
      constructor
      · intro he
        have hz : energy d k / C = 0 := by linarith
        exact (div_eq_zero_iff.mp hz).resolve_right hC.ne'
      · intro he
        simp [he]
    exact hp.trans ((energy_zero_iff d k).trans (conjugationDifference_eq_zero_iff d k))
  · intro h hh k
    simp only [p, energy, conjugationDifference_mul d hh k]

end Langlands.Archimedean

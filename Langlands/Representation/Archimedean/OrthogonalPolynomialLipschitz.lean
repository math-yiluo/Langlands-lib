import Langlands.Representation.Archimedean.OrthogonalLocalLogarithm
import Langlands.Representation.Archimedean.TrigonometricDerivativeBound
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Polynomial Lipschitz bounds on orthogonal degree subspaces -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.OrthogonalFinitePolynomial

open RealKTypeCount RealBlockFourierFinite RealBlockRotation
open RealJacquetFrobenius (entryCLM entryCLM_apply)

local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

private theorem degreeLE_le_polynomialFunctions (N : ℕ) :
    degreeLE n N ≤ (polynomialFunctions n).toSubmodule := by
  have h1 : (1 : Submodule ℂ (O n → ℂ)) ≤ (polynomialFunctions n).toSubmodule :=
    Submodule.one_le.mpr (Subalgebra.one_mem _)
  have hlin : linearSpan n ≤ (polynomialFunctions n).toSubmodule := by
    apply sup_le h1
    exact Submodule.span_le.mpr fun _ h => Algebra.subset_adjoin h
  rw [degreeLE]
  induction N with
  | zero => rwa [pow_zero]
  | succ N ih =>
    rw [pow_succ]
    exact Submodule.mul_le.mpr fun a ha b hb => (polynomialFunctions n).mul_mem (ih ha) (hlin hb)

private theorem differentiable_entryPolynomial (P : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℝ (fun A : M n => MvPolynomial.eval (fun ij => (A ij.1 ij.2 : ℂ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.eval_C]
    exact differentiable_const _
  | add a b ha hb =>
    simp only [map_add]
    exact ha.add hb
  | mul_X a ij ha =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact ha.mul (Complex.ofRealCLM.comp (entryCLM ij.1 ij.2)).differentiable

private theorem exists_differentiable_extension {N : ℕ} {f : O n → ℂ}
    (hf : f ∈ degreeLE n N) :
    ∃ F : M n → ℂ, Differentiable ℝ F ∧ ∀ k : O n, F (k : M n) = f k := by
  obtain ⟨P, hP⟩ := exists_mvPolynomial_of_mem_polynomialFunctions
    (degreeLE_le_polynomialFunctions N hf)
  exact ⟨_, differentiable_entryPolynomial P, fun k => (hP k).symm⟩

private theorem exists_perm_pair {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ e : Equiv.Perm (Fin n), e a = c ∧ e b = d := by
  let e₀ := Equiv.swap a c
  have ha : e₀ a = c := Equiv.swap_apply_left a c
  have hbc : e₀ b ≠ c := fun h => hab (e₀.injective (ha.trans h.symm))
  refine ⟨e₀.trans (Equiv.swap (e₀ b) d), ?_, ?_⟩
  · rw [Equiv.trans_apply, ha, Equiv.swap_apply_of_ne_of_ne hbc.symm hcd]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

private theorem reindex_single (e : Equiv.Perm (Fin n)) (i j : Fin n) (a : ℝ) :
    Matrix.reindexAlgEquiv ℝ ℝ e (Matrix.single i j a) = Matrix.single (e i) (e j) a := by
  ext r s
  change Matrix.single i j a (e.symm r) (e.symm s) = _
  simp only [Matrix.single_apply, e.eq_symm_apply]

private theorem reindex_unitary (e : Equiv.Perm (Fin n)) {A : M n}
    (hA : A ∈ O n) : Matrix.reindexAlgEquiv ℝ ℝ e A ∈ O n := by
  let R := Matrix.reindexAlgEquiv ℝ ℝ e
  have hstar : star (R A) = R (star A) := by ext r s; rfl
  constructor
  · rw [hstar, ← map_mul, Unitary.star_mul_self_of_mem hA, map_one]
  · rw [hstar, ← map_mul, Unitary.mul_star_self_of_mem hA, map_one]

private theorem bound_on_plane {N : ℕ} {f : C(O n, ℂ)}
    (hf : (f : O n → ℂ) ∈ degreeLE n N)
    {F : M n → ℂ} (hF : Differentiable ℝ F) (hval : ∀ k : O n, F (k : M n) = f k)
    (k : O n) (i j : Fin n) :
    ‖fderiv ℝ F (k : M n) ((k : M n) * (Matrix.single i j 1 - Matrix.single j i 1))‖ ≤
      (2 * (N : ℝ) + 1) * (N : ℝ) * ‖f‖ := by
  by_cases hij : i = j
  · subst j
    simp only [sub_self, mul_zero, map_zero, norm_zero]
    positivity
  have hn : 0 + 1 < n := by
    have hi := i.isLt
    have hj := j.isLt
    have he : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  obtain ⟨e, hea, heb⟩ := exists_perm_pair (ia_ne_ib hn) (Ne.symm hij)
  let R := Matrix.reindexAlgEquiv ℝ ℝ e
  let rot (t : ℝ) : O n := ⟨R (rotMatrix hn t), reindex_unitary e (by
    rw [← blockRotation_val_eq hn]
    exact blockRotation_mem_unitaryCompact n 0 t)⟩
  let γ (t : ℝ) := k * rot t
  have hγ : ∀ ij : Fin n × Fin n, (fun t => entry n ij (γ t)) ∈ trigPoly 1 := by
    intro ij
    let A := (k : M n)
    let P := R (blockProj hn)
    let W := R (rotationGenerator n 0)
    have h (t : ℝ) : A * R (rotMatrix hn t) =
        A + (Real.cos t - 1) • (A * P) + Real.sin t • (A * W) := by
      simp only [rotMatrix, map_add, map_one, map_smul, Matrix.mul_add, Matrix.mul_smul, mul_one, P, W]
    change (fun t => (((A * R (rotMatrix hn t)) ij.1 ij.2 : ℝ) : ℂ)) ∈ trigPoly 1
    simp_rw [h, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      (affine_mem_trigPoly (A ij.1 ij.2) ((A * P) ij.1 ij.2) ((A * W) ij.1 ij.2))
  have htrig := comp_mem_trigPoly_of_mem_degreeLE hf γ hγ
  obtain ⟨z, hz, hbound⟩ := trigonometricDerivativeBound N _ ‖f‖ (norm_nonneg f)
    htrig (fun t => f.norm_coe_le_norm (γ t)) 0
  have hReindex : R (rotationGenerator n 0) = Matrix.single i j 1 - Matrix.single j i 1 := by
    rw [rotationGenerator_eq hn, map_sub, reindex_single, reindex_single, hea, heb]
  let L := R.toLinearMap.toContinuousLinearMap
  have hB : HasDerivAt (rotMatrix hn) (rotationGenerator n 0) 0 := by
    simpa only [rotMatrix, Real.cos_zero, Real.sin_zero, sub_self, zero_smul, add_zero, mul_one] using
      hasDerivAt_rotMatrix hn 0
  have hR := (L.hasFDerivAt.comp_hasDerivAt 0 hB).const_mul (k : M n)
  have hcurve : HasDerivAt (fun t => (γ t : M n))
      ((k : M n) * (Matrix.single i j 1 - Matrix.single j i 1)) 0 := by
    change HasDerivAt (fun t => (k : M n) * R (rotMatrix hn t)) _ 0
    rw [← hReindex]
    exact hR
  have hzero : (γ 0 : M n) = (k : M n) := by
    change (k : M n) * R (rotMatrix hn 0) = _
    simp [rotMatrix]
  have hder := (hF (γ 0 : M n)).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hEq : F ∘ (fun t => (γ t : M n)) = fun t => f (γ t) := funext fun t => hval (γ t)
  rw [hzero, hEq] at hder
  rw [hder.unique hz]
  exact hbound

private theorem skew_decomposition (X : M n) (hX : Xᵀ = -X) :
    X = (1 / 2 : ℝ) • ∑ i, ∑ j, X i j • (Matrix.single i j 1 - Matrix.single j i 1) := by
  have hT : (∑ i, ∑ j, Matrix.single j i (X i j)) = Xᵀ := by
    rw [Finset.sum_comm]
    exact Matrix.sum_sum_single (fun i j => X j i)
  have hS : (∑ i, ∑ j, Matrix.single i j (X i j)) = X := Matrix.sum_sum_single X
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, Finset.sum_sub_distrib]
  rw [hT, hS, hX, smul_neg, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
  norm_num

private theorem bound_on_skew {N : ℕ} {f : C(O n, ℂ)}
    (hf : (f : O n → ℂ) ∈ degreeLE n N)
    {F : M n → ℂ} (hF : Differentiable ℝ F) (hval : ∀ k : O n, F (k : M n) = f k)
    (k : O n) (X : M n) (hX : Xᵀ = -X) :
    let A := ∑ i : Fin n, ∑ j : Fin n, ‖entryCLM i j‖
    ‖fderiv ℝ F (k : M n) ((k : M n) * X)‖ ≤
      (A / 2 * ((2 * (N : ℝ) + 1) * (N : ℝ) * ‖f‖)) * ‖X‖ := by
  let A := ∑ i : Fin n, ∑ j : Fin n, ‖entryCLM i j‖
  let B := (2 * (N : ℝ) + 1) * (N : ℝ) * ‖f‖
  let D := (fderiv ℝ F (k : M n)).comp (ContinuousLinearMap.mul ℝ (M n) (k : M n))
  let E (i j : Fin n) : M n := Matrix.single i j 1 - Matrix.single j i 1
  have hD (i j : Fin n) : ‖D (E i j)‖ ≤ B := bound_on_plane hf hF hval k i j
  change ‖D X‖ ≤ (A / 2 * B) * ‖X‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAeq : (∑ i : Fin n, ∑ j : Fin n, ‖entryCLM i j‖ * ‖X‖ * B) =
      A * ‖X‖ * B := by simp only [A, Finset.sum_mul]
  calc
    ‖D X‖ = ‖D ((1 / 2 : ℝ) • ∑ i, ∑ j, X i j • E i j)‖ := by
      rw [← skew_decomposition X hX]
    _ = (1 / 2 : ℝ) * ‖∑ i, ∑ j, X i j • D (E i j)‖ := by
      simp only [map_smul, map_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, ‖entryCLM i j‖ * ‖X‖ * B := by
      refine mul_le_mul_of_nonneg_left ?_ (show 0 ≤ (1 / 2 : ℝ) by norm_num)
      refine (norm_sum_le Finset.univ (fun i : Fin n => ∑ j, X i j • D (E i j))).trans
        (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le Finset.univ (fun j : Fin n => X i j • D (E i j))).trans
        (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul]
      exact mul_le_mul ((entryCLM i j).le_opNorm X) (hD i j) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [hAeq]
      ring

/-- The Lipschitz constant of an orthogonal entry polynomial is at most quadratic
in its degree times its supremum norm. -/
def OrthogonalPolynomialLipschitzStatement : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (f : C(O n, ℂ)),
    (f : O n → ℂ) ∈ degreeLE n N →
    ∀ x y : O n, ‖f y - f x‖ ≤ C * (1 + (N : ℝ)) ^ 2 * ‖f‖ *
      ‖(y : M n) - (x : M n)‖

theorem orthogonalPolynomialLipschitz : OrthogonalPolynomialLipschitzStatement := by
  intro n
  obtain ⟨C, hC, hLip⟩ := exists_lipschitz_bound_of_skew_derivatives n
  let A := (∑ i : Fin n, ∑ j : Fin n, ‖entryCLM i j‖) / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C * (1 + 3 * A), by positivity, fun N f hf x y => ?_⟩
  obtain ⟨F, hF, hval⟩ := exists_differentiable_extension hf
  let B := A * ((2 * (N : ℝ) + 1) * (N : ℝ) * ‖f‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hder (k : O n) (X : M n) (hX : Xᵀ = -X) : ∃ z : ℂ,
      HasDerivAt (fun s : ℝ => f (k * InductionStages.expCurve X hX s)) z 0 ∧ ‖z‖ ≤ B * ‖X‖ := by
    let γ (s : ℝ) := k * InductionStages.expCurve X hX s
    have hE : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
      simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
        hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    have hγ : HasDerivAt (fun s => (γ s : M n)) ((k : M n) * X) 0 := hE.const_mul _
    have hzero : (γ 0 : M n) = (k : M n) := by simp [γ, InductionStages.expCurve_zero]
    have h := (hF (γ 0 : M n)).hasFDerivAt.comp_hasDerivAt 0 hγ
    have he : F ∘ (fun t => (γ t : M n)) = fun t => f (γ t) := funext fun t => hval (γ t)
    rw [hzero, he] at h
    exact ⟨_, h, bound_on_skew hf hF hval k X hX⟩
  have hpoly : (2 * (N : ℝ) + 1) * (N : ℝ) ≤ 3 * (1 + (N : ℝ)) ^ 2 := by
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  have hunit : (1 : ℝ) ≤ (1 + (N : ℝ)) ^ 2 := by
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  have hFactor : ‖f‖ + B ≤ (1 + 3 * A) * (1 + (N : ℝ)) ^ 2 * ‖f‖ := calc
    _ = (1 + A * ((2 * (N : ℝ) + 1) * (N : ℝ))) * ‖f‖ := by dsimp [B]; ring
    _ ≤ ((1 + (N : ℝ)) ^ 2 + A * (3 * (1 + (N : ℝ)) ^ 2)) * ‖f‖ :=
      mul_le_mul_of_nonneg_right (add_le_add hunit (mul_le_mul_of_nonneg_left hpoly hA)) (norm_nonneg _)
    _ = _ := by ring
  calc
    _ ≤ C * (‖f‖ + B) * ‖(y : M n) - (x : M n)‖ := hLip f B hB hder x y
    _ ≤ C * ((1 + 3 * A) * (1 + (N : ℝ)) ^ 2 * ‖f‖) * ‖(y : M n) - (x : M n)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFactor hC.le) (norm_nonneg _)
    _ = _ := by ring

end Langlands.Archimedean.OrthogonalFinitePolynomial

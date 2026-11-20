import Langlands.Representation.Archimedean.GeneralLinear
import Langlands.Global.Hecke.MixedSpaceFourier
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Unitary translate finiteness of complex polynomial Gaussians -/

noncomputable section

open Langlands.Archimedean
open scoped Matrix ContDiff Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

/-- Both the entries and their conjugates are polynomial variables. -/
abbrev ComplexMatrixPolynomialIndex (m n : ℕ) :=
  (Fin m × Fin n) ⊕ (Fin m × Fin n)

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin m) (Fin n) ℂ
local notation "Square" => Matrix (Fin m) (Fin m) ℂ
local notation "Idx" => ComplexMatrixPolynomialIndex m n
local notation "Poly" => MvPolynomial Idx ℂ

/-- The two sets of polynomial coordinates of a complex matrix. -/
def complexMatrixPolynomialCoordinates (X : Mat) : Idx → ℂ
  | .inl (i, j) => X i j
  | .inr (i, j) => starRingEnd ℂ (X i j)

private def matrixSquareNorm (X : Mat) : ℝ :=
  ∑ i, ∑ j, ‖X i j‖ ^ 2

private theorem matrixSquareNorm_trace (X : Mat) :
    matrixSquareNorm X = (Xᴴ * X).trace.re := by
  have h : (Xᴴ * X).trace = ((∑ j, ∑ i, ‖X i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      ← starRingEnd_apply, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re, matrixSquareNorm, Finset.sum_comm]

private theorem matrixSquareNorm_unitary_left (k : unitaryCompact ℂ m) (X : Mat) :
    matrixSquareNorm (k.val.val * X) = matrixSquareNorm X := by
  have hk : (k.val.val)ᴴ * k.val.val = 1 := Unitary.star_mul_self_of_mem k.2
  have h : (k.val.val * X)ᴴ * (k.val.val * X) = Xᴴ * X := by
    calc
      _ = Xᴴ * ((k.val.val)ᴴ * k.val.val) * X := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hk, Matrix.mul_one]
  rw [matrixSquareNorm_trace, matrixSquareNorm_trace, h]

/-- A polynomial in the complex entries and their conjugates times a
Gaussian of the squared matrix norm. Jacquet uses `t = 2 * π`. -/
def complexMatrixPolynomialGaussian (t : ℝ) (p : Poly) (X : Mat) : ℂ :=
  MvPolynomial.aeval (complexMatrixPolynomialCoordinates X) p *
    Complex.exp (-((t * matrixSquareNorm X : ℝ) : ℂ))

private def leftVariables (A : Square) : Idx → Poly
  | .inl (i, j) => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X (.inl (k, j))
  | .inr (i, j) => ∑ k, MvPolynomial.C (starRingEnd ℂ (A i k)) * MvPolynomial.X (.inr (k, j))

private theorem totalDegree_leftVariables (A : Square) (i : Idx) :
    (leftVariables A i).totalDegree ≤ 1 := by
  rcases i with ⟨i, j⟩ | ⟨i, j⟩ <;>
    apply MvPolynomial.totalDegree_finsetSum_le <;> intro k _ <;>
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp only
      [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl])

private theorem eval_leftVariables (A : Square) (X : Mat) :
    (fun i => MvPolynomial.aeval (complexMatrixPolynomialCoordinates X) (leftVariables A i)) =
      complexMatrixPolynomialCoordinates (A * X) := by
  funext i
  rcases i with ⟨i, j⟩ | ⟨i, j⟩ <;>
    simp only [leftVariables, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply, complexMatrixPolynomialCoordinates, Matrix.mul_apply]

private theorem totalDegree_bind_leftVariables (A : Square) (p : Poly) :
    (MvPolynomial.bind₁ (leftVariables A) p).totalDegree ≤ p.totalDegree := by
  classical
  have hsum : MvPolynomial.bind₁ (leftVariables A) p =
      ∑ d ∈ p.support, MvPolynomial.bind₁ (leftVariables A) (MvPolynomial.monomial d (p.coeff d)) := by
    rw [← map_sum, ← p.as_sum]
  rw [hsum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.bind₁_monomial]
  calc
    _ ≤ (MvPolynomial.C (p.coeff d) : Poly).totalDegree +
        (∏ i ∈ d.support, leftVariables A i ^ d i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum ?_)
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left _ (totalDegree_leftVariables A i)).trans_eq (Nat.mul_one _))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd

private def polynomialGaussianLinear (t : ℝ) : Poly →ₗ[ℂ] (Mat → ℂ) where
  toFun := complexMatrixPolynomialGaussian t
  map_add' p q := by
    funext X
    simp only [complexMatrixPolynomialGaussian, map_add, Pi.add_apply, add_mul]
  map_smul' c p := by
    funext X
    simp only [complexMatrixPolynomialGaussian, map_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, RingHom.id_apply]

private theorem norm_sq_le_matrixSquareNorm (X : Mat) : ‖X‖ ^ 2 ≤ matrixSquareNorm X := by
  have h0 : 0 ≤ matrixSquareNorm X := by unfold matrixSquareNorm; positivity
  have h : ‖X‖ ≤ Real.sqrt (matrixSquareNorm X) :=
    (Matrix.norm_le_iff (Real.sqrt_nonneg _)).mpr fun i j => by
      apply (Real.le_sqrt (norm_nonneg _) h0).mpr
      exact (Finset.single_le_sum (fun a _ => sq_nonneg ‖X i a‖) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun a => ∑ b, ‖X a b‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ i))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (Real.sq_sqrt h0)

private def gaussianExponent (t : ℝ) (X : Mat) : ℝ := -(t * matrixSquareNorm X)

private def entryCLM (i : Fin m) (j : Fin n) : Mat →L[ℂ] ℂ where
  toFun X := X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

private theorem gaussianExponent_temperate (t : ℝ) :
    (gaussianExponent (m := m) (n := n) t).HasTemperateGrowth := by
  unfold gaussianExponent matrixSquareNorm
  have entry (i : Fin m) (j : Fin n) : (fun X : Mat => X i j).HasTemperateGrowth :=
    ((entryCLM i j).restrictScalars ℝ).hasTemperateGrowth
  have hnorm (i : Fin m) (j : Fin n) : (fun X : Mat => ‖X i j‖ ^ 2).HasTemperateGrowth := by
    have hr := Complex.reCLM.hasTemperateGrowth.comp (entry i j)
    have hi := Complex.imCLM.hasTemperateGrowth.comp (entry i j)
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    exact (hr.mul hr).add (hi.mul hi)
  fun_prop

private def radialSchwartz (t : ℝ) (ht : 0 < t) : SchwartzMap Mat ℝ where
  toFun := Real.exp ∘ gaussianExponent t
  smooth' := Real.contDiff_exp.comp (gaussianExponent_temperate t).1
  decay' k j := by
    have hE := gaussianExponent_temperate (m := m) (n := n) t
    obtain ⟨l, C, _, hderiv⟩ := hE.norm_iteratedFDeriv_le_uniform j
    obtain ⟨B, _, hgauss⟩ := Langlands.Global.Hecke.exists_exp_neg_mul_sq_le_rpow ht
      ((k + l * j : ℕ) : ℝ)
    let A := max 1 C
    refine ⟨(j.factorial : ℝ) * A ^ j * B, fun X => ?_⟩
    let R := 1 + ‖X‖
    have hR : 1 ≤ R := le_add_of_nonneg_right (norm_nonneg X)
    have hA : 1 ≤ A := le_max_left _ _
    have hD : 1 ≤ A * R ^ l := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hR)
    have hbound := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := gaussianExponent t) (n := j)
      Real.contDiff_exp hE.1 (by exact_mod_cast le_top) X
      (C := Real.exp (gaussianExponent t X)) (D := A * R ^ l)
      (fun i _ => by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp, Real.norm_eq_abs, Real.abs_exp])
      (fun i hi hin => (hderiv i hin X).trans <|
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans
          (le_self_pow₀ hD (by omega)))
    have hdecay : R ^ (k + l * j) * Real.exp (gaussianExponent t X) ≤ B := by
      have h := hgauss ‖X‖ (norm_nonneg X)
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, le_mul_inv_iff₀ (by positivity)] at h
      rw [mul_comm] at h
      refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)).trans h
      exact neg_le_neg (mul_le_mul_of_nonneg_left (norm_sq_le_matrixSquareNorm X) ht.le)
    calc
      ‖X‖ ^ k * ‖iteratedFDeriv ℝ j (Real.exp ∘ gaussianExponent t) X‖
          ≤ R ^ k * ((j.factorial : ℝ) * Real.exp (gaussianExponent t X) * (A * R ^ l) ^ j) := by
            gcongr
            exact le_add_of_nonneg_left zero_le_one
      _ = (j.factorial : ℝ) * A ^ j * (R ^ (k + l * j) * Real.exp (gaussianExponent t X)) := by
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      _ ≤ (j.factorial : ℝ) * A ^ j * B := mul_le_mul_of_nonneg_left hdecay (by positivity)

private theorem polynomialEval_temperate (p : Poly) :
    (fun X : Mat => MvPolynomial.aeval (complexMatrixPolynomialCoordinates X) p).HasTemperateGrowth := by
  have hCoord (i : Idx) : (fun X : Mat => complexMatrixPolynomialCoordinates X i).HasTemperateGrowth := by
    rcases i with ⟨i, j⟩ | ⟨i, j⟩
    · exact ((entryCLM i j).restrictScalars ℝ).hasTemperateGrowth
    · exact Complex.conjCLE.hasTemperateGrowth.comp ((entryCLM i j).restrictScalars ℝ).hasTemperateGrowth
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply] using
      (Function.HasTemperateGrowth.const (E := Mat) c)
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.aeval_X] using hp.fun_mul (hCoord i)

/-- The polynomial Gaussian with positive scale, as an actual Schwartz test. -/
def complexMatrixPolynomialGaussianSchwartz (t : ℝ) (ht : 0 < t) (p : Poly) : SchwartzMap Mat ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun X => MvPolynomial.aeval (complexMatrixPolynomialCoordinates X) p)
    ((radialSchwartz t ht).postcompCLM Complex.ofRealCLM)

theorem complexMatrixPolynomialGaussianSchwartz_apply (t : ℝ) (ht : 0 < t) (p : Poly) (X : Mat) :
    complexMatrixPolynomialGaussianSchwartz t ht p X = complexMatrixPolynomialGaussian t p X := by
  rw [complexMatrixPolynomialGaussianSchwartz, SchwartzMap.smulLeftCLM_apply_apply
    (polynomialEval_temperate p), SchwartzMap.postcompCLM_apply]
  change MvPolynomial.aeval (complexMatrixPolynomialCoordinates X) p *
    (Real.exp (gaussianExponent t X) : ℂ) = _
  rw [Complex.ofReal_exp, complexMatrixPolynomialGaussian, gaussianExponent, Complex.ofReal_neg]

variable (m n) in
/-- The continuous polynomial Gaussians used in complex Jacquet integrals
have finite-dimensional span under unitary left translations. -/
def ComplexLocalPolynomialGaussianStatement : Prop :=
  ∀ (t : ℝ) (p : Poly), Continuous (complexMatrixPolynomialGaussian t p) ∧
    (FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ m =>
      fun X : Mat => complexMatrixPolynomialGaussian t p ((k.val⁻¹).val * X)))) ∧
    (0 < t → ∃ Φ : SchwartzMap Mat ℂ, (Φ : Mat → ℂ) = complexMatrixPolynomialGaussian t p)

theorem complexLocalPolynomialGaussian : ComplexLocalPolynomialGaussianStatement m n := by
  intro t p
  refine ⟨?_, ?_, fun ht => ⟨complexMatrixPolynomialGaussianSchwartz t ht p,
    funext (complexMatrixPolynomialGaussianSchwartz_apply t ht p)⟩⟩
  · have hCoords : Continuous (complexMatrixPolynomialCoordinates (m := m) (n := n)) := by
      apply continuous_pi
      intro i
      rcases i with ⟨i, j⟩ | ⟨i, j⟩
      · exact (continuous_apply j).comp (continuous_apply i)
      · have h : Continuous fun X : Mat => X i j := (continuous_apply j).comp (continuous_apply i)
        exact h.star
    have hnorm : Continuous (matrixSquareNorm (m := m) (n := n)) := by
      unfold matrixSquareNorm
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (((continuous_apply j).comp (continuous_apply i)).norm.pow 2)
    exact ((MvPolynomial.continuous_eval p).comp hCoords).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul hnorm)).neg)
  · let V := MvPolynomial.restrictTotalDegree Idx ℂ p.totalDegree
    let W := V.map (polynomialGaussianLinear t)
    apply Submodule.finiteDimensional_of_le (S₂ := W)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    let A := (k⁻¹ : unitaryCompact ℂ m).val.val
    refine ⟨MvPolynomial.bind₁ (leftVariables A) p,
      (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (totalDegree_bind_leftVariables A p), ?_⟩
    funext X
    change complexMatrixPolynomialGaussian t (MvPolynomial.bind₁ (leftVariables A) p) X =
      complexMatrixPolynomialGaussian t p ((k.val⁻¹).val * X)
    have hnorm : matrixSquareNorm ((k.val⁻¹).val * X) = matrixSquareNorm X :=
      matrixSquareNorm_unitary_left k⁻¹ X
    simp only [complexMatrixPolynomialGaussian, hnorm, MvPolynomial.aeval_bind₁,
      eval_leftVariables, A]
    rfl

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet

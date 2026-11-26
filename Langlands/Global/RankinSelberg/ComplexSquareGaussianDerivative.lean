import Langlands.Global.RankinSelberg.ComplexSquareZetaUnit
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! # Linear directional derivatives of square polynomial Gaussians -/

noncomputable section

open MvPolynomial
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinates_re coordinates_im
  matrixSqNorm coordinatePartCLM)

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "I" => Coordinates n n
local notation "Poly" => MvPolynomial I ℂ

/-- A directional derivative along a continuous real-linear vector field on square matrices. -/
def squareDirectionalTest (A : Mat →L[ℝ] Mat) : 𝓢(Mat, ℂ) →L[ℝ] 𝓢(Mat, ℂ) :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℂ).flip A.hasTemperateGrowth).comp
    (SchwartzMap.fderivCLM ℝ Mat ℂ)

@[simp] theorem squareDirectionalTest_apply (A : Mat →L[ℝ] Mat) (Φ : 𝓢(Mat, ℂ)) (Y : Mat) :
    squareDirectionalTest A Φ Y = fderiv ℝ Φ Y (A Y) := rfl

private def coordLinear (i : I) : Mat →L[ℝ] ℂ :=
  (coordinatePartCLM i.2.2).comp
    ({ toFun := fun A => A i.1 i.2.1
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : Mat →ₗ[ℝ] ℂ).toContinuousLinearMap

private theorem matrix_sum_single (Y : Mat) :
    (∑ i : Fin n, ∑ j : Fin n, ((Y i j).re • Matrix.single i j (1 : ℂ) +
      (Y i j).im • Matrix.single i j Complex.I)) = Y := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
    · simpa only [and_self, ite_true, Complex.real_smul, mul_one] using Complex.re_add_im (Y i j)
    · intro b _ hb
      simp [hb]
  · intro b _ hb
    simp [hb]

private def linearCoordinatePolynomial (A : Mat →L[ℝ] Mat) (i : I) : Poly :=
  ∑ j : Fin n, ∑ k : Fin n,
    (C (coordLinear i (A (Matrix.single j k 1))) * X (j, k, false) +
      C (coordLinear i (A (Matrix.single j k Complex.I))) * X (j, k, true))

private theorem eval_linearCoordinatePolynomial (A : Mat →L[ℝ] Mat) (Y : Mat) (i : I) :
    eval (coordinates Y) (linearCoordinatePolynomial A i) = coordinates (A Y) i := by
  have he := congrArg (fun Z => coordLinear i (A Z)) (matrix_sum_single Y)
  change eval (coordinates Y) (linearCoordinatePolynomial A i) = coordLinear i (A Y)
  rw [← he]
  simp only [linearCoordinatePolynomial, map_sum, map_add, map_mul, eval_C, eval_X,
    map_smul, Complex.real_smul, coordinates_re, coordinates_im]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem hasDerivAt_evaluation (q : Poly) (A : Mat →L[ℝ] Mat) :
    ∃ q' : Poly, ∀ (Y : Mat) (γ : ℝ → Mat), γ 0 = Y → HasDerivAt γ (A Y) 0 →
      HasDerivAt (fun t => eval (coordinates (γ t)) q) (eval (coordinates Y) q') 0 := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun Y γ hγ hD => ?_⟩
    simpa only [eval_C, map_zero] using (hasDerivAt_const (0 : ℝ) a)
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', fun Y γ hγ hD => ?_⟩
    simpa only [map_add, Pi.add_def] using (hp' Y γ hγ hD).add (hq' Y γ hγ hD)
  | mul_X q i hq =>
    obtain ⟨q', hq'⟩ := hq
    refine ⟨q' * X i + q * linearCoordinatePolynomial A i, fun Y γ hγ hD => ?_⟩
    have hCoord := (coordLinear i).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD
    have hCoord' : HasDerivAt (fun t => coordinates (γ t) i) (coordinates (A Y) i) 0 := hCoord
    simpa only [map_mul, map_add, eval_X, eval_linearCoordinatePolynomial, Pi.mul_def, hγ] using
      (hq' Y γ hγ hD).mul hCoord'

private def squaredNormPolynomial : Poly :=
  ∑ i : Fin n, ∑ j : Fin n, (X (i, j, false) ^ 2 + X (i, j, true) ^ 2)

private theorem eval_squaredNormPolynomial (Y : Mat) :
    eval (coordinates Y) squaredNormPolynomial = (matrixSqNorm Y : ℂ) := by
  simp only [squaredNormPolynomial, matrixSqNorm, Complex.ofReal_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_pow, eval_X, coordinates_re, coordinates_im,
    ← Complex.ofReal_pow, ← Complex.ofReal_add]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- A real-linear directional derivative preserves square polynomial Gaussians of scale `2π`. -/
def ComplexSquareGaussianDerivativeStatement : Prop :=
  ∀ (A : Mat →L[ℝ] Mat) (Φ : 𝓢(Mat, ℂ)) (q : Poly),
    (Φ : Mat → ℂ) = squarePolynomialGaussian q →
    ∃ p : Poly, (squareDirectionalTest A Φ : Mat → ℂ) = squarePolynomialGaussian p

theorem complexSquareGaussianDerivative : ComplexSquareGaussianDerivativeStatement (n := n) := by
  intro A Φ q hΦ
  obtain ⟨p, hp⟩ := hasDerivAt_evaluation q A
  obtain ⟨Q, hQ⟩ := hasDerivAt_evaluation squaredNormPolynomial A
  refine ⟨p + q * C (-(2 * (Real.pi : ℂ))) * Q, ?_⟩
  funext Y
  let γ (t : ℝ) : Mat := Y + t • A Y
  have hγ : γ 0 = Y := by simp [γ]
  have hD : HasDerivAt γ (A Y) 0 := by
    simpa [γ] using ((hasDerivAt_id (0 : ℝ)).smul_const (A Y)).const_add Y
  have hF : HasDerivAt (fun t => Φ (γ t)) (squareDirectionalTest A Φ Y) 0 := by
    rw [squareDirectionalTest_apply]
    simpa only [Function.comp_def, hγ] using (Φ.hasFDerivAt (γ 0)).comp_hasDerivAt (0 : ℝ) hD
  have hn := hQ Y γ hγ hD
  simp only [eval_squaredNormPolynomial] at hn
  have hG := (hn.const_mul (-(2 * (Real.pi : ℂ)))).cexp
  let g (Z : Mat) : ℂ := Real.exp (-(2 * Real.pi) * matrixSqNorm Z)
  have hG' : HasDerivAt (fun t => g (γ t))
      (g Y * (-(2 * (Real.pi : ℂ)) * eval (coordinates Y) Q)) 0 := by
    simpa only [g, hγ, ← Complex.ofReal_mul, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_neg, Complex.ofReal_exp] using hG
  rw [hΦ] at hF
  rw [hF.unique ((hp Y γ hγ hD).mul hG')]
  change eval (coordinates Y) p * g (γ 0) + eval (coordinates (γ 0)) q *
    (g Y * (-(2 * (Real.pi : ℂ)) * eval (coordinates Y) Q)) = eval (coordinates Y) _ * g Y
  simp only [hγ, map_add, map_mul, eval_C]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

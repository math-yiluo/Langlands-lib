import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Langlands.Representation.Archimedean.ComplexLevelFunctions

/-!
# The torus derivative of a principal-series function

For characters `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}` and `f` in the principal series of `χ`,
`fderiv_unitsExtension_diagonal_mul` computes the derivative of the extension `unitsExtension f`
at a unit `y` along `diag(d) y`: it is `torusDeriv l t d · f(y)` with
`torusDeriv l t d = Σ_k (l_k i Im d_k + 2 τ_k Re d_k)` and `τ_k = t_k + (n-1)/2 - k`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate ContDiff

set_option autoImplicit false

namespace Langlands.Archimedean.LevelFunctions

open Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The derivative of the torus character. -/
def torusDeriv (l : ℕ → ℤ) (t : ℕ → ℂ) (d : Fin n → ℂ) : ℂ :=
  ∑ k : Fin n, ((l k : ℂ) * Complex.I * ((d k).im : ℂ) +
    2 * (t k + ((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ)) * ((d k).re : ℂ))

theorem phase_exp (w : ℂ) : phase (Units.mk0 (Complex.exp w) (Complex.exp_ne_zero w)) =
    Complex.exp (Complex.I * (w.im : ℂ)) := by
  unfold phase
  simp only [Units.val_mk0, Complex.norm_exp]
  rw [div_eq_iff (by exact_mod_cast (Real.exp_pos _).ne'), Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  conv_lhs => rw [← Complex.re_add_im w]
  ring

theorem norm_exp_cpow (w s : ℂ) :
    ((‖Complex.exp w‖ : ℝ) : ℂ) ^ (2 * s) = Complex.exp (2 * (w.re : ℂ) * s) := by
  rw [Complex.norm_exp, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp]
  · ring_nf
  · simp [Real.pi_pos]
  · simp [Real.pi_pos.le]

/-- The character of `diag(exp(s d_k))` is `exp(s · torusDeriv l t d)`. -/
theorem principalSeriesCharacter_exp {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k)) (d : Fin n → ℂ) (s : ℝ) :
    principalSeriesCharacter ℂ n χ
        (fun k => Units.mk0 (Complex.exp ((s : ℂ) * d k)) (Complex.exp_ne_zero _)) =
      Complex.exp ((s : ℂ) * torusDeriv l t d) := by
  unfold principalSeriesCharacter torusDeriv
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hχ, phase_exp, ← Complex.exp_int_mul, Units.val_mk0, norm_exp_cpow,
    Complex.finrank_real_complex, ComplexDuality.LieInvariance.ofReal_norm_exp_sq_cpow,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero]
  push_cast
  ring

/-- **The torus derivative.** -/
theorem fderiv_unitsExtension_diagonal_mul {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ) (d : Fin n → ℂ)
    (y : Langlands.GeneralLinear n ℂ) :
    fderiv ℝ (unitsExtension f) (y : Matrix (Fin n) (Fin n) ℂ)
        (Matrix.diagonal d * (y : Matrix (Fin n) (Fin n) ℂ)) = torusDeriv l t d * f y := by
  have hfs := ((mem_principalSeries_iff ℂ n χ f).1 hf).1
  have hd := differentiableAt_unitsExtension hfs (Units.isUnit y)
  set Λ := torusDeriv l t d
  let a : ℝ → Fin n → ℂˣ := fun s k => Units.mk0 (Complex.exp ((s : ℂ) * d k))
    (Complex.exp_ne_zero _)
  have hexp : ∀ s : ℝ, NormedSpace.exp (s • Matrix.diagonal d) =
      Matrix.diagonal fun k => (a s k : ℂ) := fun s => by
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext k
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    simp [a, Complex.real_smul]
  have hγ : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • Matrix.diagonal d) *
      (y : Matrix (Fin n) (Fin n) ℂ)) (Matrix.diagonal d * (y : Matrix (Fin n) (Fin n) ℂ)) 0 := by
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.diagonal d) 0).mul_const
      (y : Matrix (Fin n) (Fin n) ℂ)
    simpa using h
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hfun : (unitsExtension f ∘ fun s : ℝ => NormedSpace.exp (s • Matrix.diagonal d) *
      (y : Matrix (Fin n) (Fin n) ℂ)) = fun s : ℝ => Complex.exp ((s : ℂ) * Λ) * f y := by
    funext s
    simp only [Function.comp_apply, hexp]
    rw [ComplexDuality.LieInvariance.unitsExtension_diagonal_mul hf,
      principalSeriesCharacter_exp l t hχ d s]
  rw [hfun] at hcomp
  have hd' : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Λ) * f y) (Λ * f y) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Λ).cexp).mul_const (f y)
    simpa using h
  exact hcomp.unique hd'

end Langlands.Archimedean.LevelFunctions

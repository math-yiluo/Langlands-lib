import Langlands.Analysis.Complex.PolynomialGaussianFourier
import Langlands.Global.RankinSelberg.RealEqualPolynomialGeneration
import Langlands.Global.RankinSelberg.RealGodementRowFourierInversion

/-! # Real Fourier closure of standard polynomial Gaussian rows -/

noncomputable section

open MvPolynomial
open scoped FourierTransform SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open Langlands.Analysis.PolynomialGaussianFourier
open RealEqualPolynomialGeneration (IsGaussianPolynomialRow)

variable {r : ℕ}

local notation "Idx" => Fin (r + 1)
local notation "Row" => (Idx → ℝ)
local notation "EuclideanRow" => EuclideanSpace ℝ Idx

private abbrev rowEquiv : EuclideanRow ≃L[ℝ] Row :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Idx => ℝ)

private theorem row_coordinates (x : EuclideanRow) :
    coordinates (EuclideanSpace.basisFun Idx ℝ) x = fun i => (x i : ℂ) := by
  funext i
  simp [coordinates, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]

private theorem row_norm_sq (x : EuclideanRow) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

/-- The actual positive row transform at either unit real scale preserves polynomial
Gaussian rows at scale `π`. -/
def RealStandardGaussianFourierStatement : Prop :=
  ∀ (a : ℝˣ), |(a : ℝ)| = 1 → ∀ (Φ : 𝓢(Row, ℂ)),
    IsGaussianPolynomialRow Real.pi Φ →
      IsGaussianPolynomialRow Real.pi (realRowSchwartzFourier (r + 1) a Φ)

theorem realStandardGaussianFourier : RealStandardGaussianFourierStatement (r := r) := by
  intro a ha Φ hΦ
  obtain ⟨p, hp⟩ := hΦ
  let Ψ : 𝓢(EuclideanRow, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rowEquiv Φ
  have hΨ (x : EuclideanRow) : Ψ x =
      eval (coordinates (EuclideanSpace.basisFun Idx ℝ) x) p * gaussian Real.pi x := by
    change Φ (rowEquiv x) = _
    rw [hp, row_coordinates, gaussian, row_norm_sq, neg_mul]
    rfl
  obtain ⟨q, hq⟩ := exists_polynomial_fourier (EuclideanSpace.basisFun Idx ℝ)
    Real.pi Real.pi_pos Ψ p hΨ
  let vars : Idx → MvPolynomial Idx ℂ := fun i => C (-(a : ℝ) : ℂ) * X i
  refine ⟨bind₁ vars q, fun x => ?_⟩
  change scaledEuclideanFourier a Ψ (rowEquiv.symm x) =
    eval (fun i => (x i : ℂ)) (bind₁ vars q) * (Real.exp (-Real.pi * ∑ i, x i ^ 2) : ℂ)
  have hHaar : euclideanHaarFactor a EuclideanRow = 1 := by
    simp [euclideanHaarFactor, ha]
  rw [scaledEuclideanFourier_apply, hHaar, Complex.ofReal_one, one_mul,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourier_coe,
    hq, gaussian, row_coordinates]
  have hEval : eval (fun i => (x i : ℂ)) (bind₁ vars q) =
      eval (fun i => ((-((a : ℝ) • rowEquiv.symm x) : EuclideanRow) i : ℂ)) q := by
    have hVars (i : Idx) : eval (fun j => (x j : ℂ)) (vars i) =
        ((-((a : ℝ) • rowEquiv.symm x) : EuclideanRow) i : ℂ) := by
      change eval (fun j => (x j : ℂ)) (vars i) = (-((a : ℝ) * x i) : ℝ)
      simp [vars]
    simpa only [aeval_eq_eval, hVars] using aeval_bind₁ (fun i => (x i : ℂ)) vars q
  rw [hEval, norm_neg, norm_smul, Real.norm_eq_abs, ha, one_mul,
    row_norm_sq, pow_two Real.pi, mul_div_cancel_right₀ _ Real.pi_ne_zero, neg_mul]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealGodement

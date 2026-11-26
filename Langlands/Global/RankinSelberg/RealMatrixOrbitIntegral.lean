import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiating an equality of weighted real principal-series evaluations -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open MeasureTheory Filter Set Topology
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealPlaceRestriction

local instance realOrbitGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance realOrbitGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩

variable {r : ℕ} {ds : List RealBlock}
local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "P" => principalSeries ℝ n (realPositionCharacter ds)
local notation "H" => @realMatrixHeight n

/-- The weighted orbit word for a fixed evaluation point is integrable. -/
theorem integrable_mul_orbitWord (μ : Measure G) {W : G → ℂ} (hW : AEStronglyMeasurable W μ)
    (hI : ∀ m : ℕ, Integrable (fun g => ‖W g‖ * H g ^ m) μ)
    {τ : G → G} (hτ : Continuous τ) (hτH : ∀ g, H (τ g) = H g)
    (Xs : List Mat) (f : P) (x : G) :
    Integrable (fun g => W g * orbitWord r ds Xs f (τ g) x) μ := by
  obtain ⟨N, hN⟩ := exists_uniform_orbitWord_height r ds
  obtain ⟨C, _, hc⟩ := hN Xs f
  have hcon := (continuous_orbitWord r ds Xs f).comp (hτ.prodMk continuous_const :
    Continuous (fun g : G => (τ g, x)))
  refine ((hI (N + Xs.length)).const_mul (C * H x ^ N)).mono'
    (hW.mul hcon.aestronglyMeasurable) (ae_of_all μ fun g => ?_)
  rw [norm_mul]
  have h := hc (τ g) x
  rw [hτH] at h
  calc
    _ ≤ ‖W g‖ * (C * H x ^ N * H g ^ (N + Xs.length)) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

/-- Derivative of the weighted orbit integral along the right exponential curve through `x`. -/
theorem hasDerivAt_integral_orbitWord (μ : Measure G) {W : G → ℂ} (hW : AEStronglyMeasurable W μ)
    (hI : ∀ m : ℕ, Integrable (fun g => ‖W g‖ * H g ^ m) μ)
    {τ : G → G} (hτ : Continuous τ) (hτH : ∀ g, H (τ g) = H g)
    (Xs : List Mat) (f : P) (X : Mat) (x : G) :
    HasDerivAt (fun t : ℝ => ∫ g, W g * orbitWord r ds Xs f (τ g) (x * matrixExpUnit n (t • X)) ∂μ)
      (∫ g, W g * orbitWord r ds (X :: Xs) f (τ g) x ∂μ) 0 := by
  let path (t : ℝ) := x * matrixExpUnit n (t • X)
  have hpath : Continuous path := continuous_const.mul (KIntegralInvariance.continuous_matrixExpUnit_smul X)
  have hp0 : path 0 = x := by simp only [path, zero_smul, matrixExpUnit_zero, mul_one]
  let S := Icc (-1 : ℝ) 1
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_realMatrixHeight.comp hpath).continuousOn
  have hBH (t : ℝ) (ht : t ∈ S) : H (path t) ≤ max B 0 :=
    (Real.le_norm_self _).trans ((hB t ht).trans (le_max_left _ _))
  obtain ⟨N, hN⟩ := exists_uniform_orbitWord_height r ds
  obtain ⟨C, hC, hc⟩ := hN (X :: Xs) f
  let F (t : ℝ) (g : G) := W g * orbitWord r ds Xs f (τ g) (path t)
  let J (t : ℝ) (g : G) := W g * orbitWord r ds (X :: Xs) f (τ g) (path t)
  have hF (t : ℝ) : Integrable (F t) μ := integrable_mul_orbitWord μ hW hI hτ hτH Xs f (path t)
  have hJ (t : ℝ) : Integrable (J t) μ := integrable_mul_orbitWord μ hW hI hτ hτH (X :: Xs) f (path t)
  let bound (g : G) := C * (max B 0) ^ N * (‖W g‖ * H g ^ (N + (X :: Xs).length))
  have hb : Integrable bound μ := (hI _).const_mul _
  have hle : ∀ᵐ g ∂μ, ∀ t ∈ S, ‖J t g‖ ≤ bound g := ae_of_all μ fun g t ht => by
    have h := hc (τ g) (path t)
    rw [hτH] at h
    have hl := pow_le_pow_left₀ (realMatrixHeight_nonneg (path t)) (hBH t ht) N
    have h₁ := mul_le_mul_of_nonneg_left hl hC
    have h₂ := mul_le_mul_of_nonneg_right h₁ (pow_nonneg (realMatrixHeight_nonneg g) (N + (X :: Xs).length))
    change ‖W g * orbitWord r ds (X :: Xs) f (τ g) (path t)‖ ≤ bound g
    rw [norm_mul]
    calc
      _ ≤ ‖W g‖ * (C * H (path t) ^ N * H g ^ (N + (X :: Xs).length)) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ ≤ ‖W g‖ * (C * max B 0 ^ N * H g ^ (N + (X :: Xs).length)) :=
        mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
      _ = _ := by dsimp [bound]; ring
  have hder : ∀ᵐ g ∂μ, ∀ t ∈ S, HasDerivAt (F · g) (J t g) t := ae_of_all μ fun g t _ => by
    have h := KIntegralInvariance.hasDerivAt_mul_matrixExpUnit_at
      (smooth_orbitWord_point r ds Xs f (τ g)) x X t
    simpa only [F, J, path, orbitWord_cons, Pi.smul_def, smul_eq_mul] using h.const_smul (W g)
  obtain ⟨_, ht⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable) (hF 0) (hJ 0).aestronglyMeasurable hle hb hder
  simpa only [F, J, hp0, path] using ht

/-- Equality of two weighted orbit evaluations at every point propagates to every derivative
word. The two translation maps may differ but both preserve the height. -/
theorem integral_orbitWord_eq_of_evaluation_eq (μ : Measure G) {W W' : G → ℂ}
    (hW : AEStronglyMeasurable W μ) (hW' : AEStronglyMeasurable W' μ)
    (hI : ∀ m : ℕ, Integrable (fun g => ‖W g‖ * H g ^ m) μ)
    (hI' : ∀ m : ℕ, Integrable (fun g => ‖W' g‖ * H g ^ m) μ)
    {τ τ' : G → G} (hτ : Continuous τ) (hτ' : Continuous τ')
    (hτH : ∀ g, H (τ g) = H g) (hτH' : ∀ g, H (τ' g) = H g) (f : P)
    (hE : ∀ x : G, (∫ g, W g * (f : G → ℂ) (x * τ g) ∂μ) =
      ∫ g, W' g * (f : G → ℂ) (x * τ' g) ∂μ) :
    ∀ (Xs : List Mat) (x : G), (∫ g, W g * orbitWord r ds Xs f (τ g) x ∂μ) =
      ∫ g, W' g * orbitWord r ds Xs f (τ' g) x ∂μ := by
  intro Xs
  induction Xs with
  | nil => simpa only [orbitWord_nil] using hE
  | cons X Xs ih =>
    intro x
    have h := hasDerivAt_integral_orbitWord μ hW hI hτ hτH Xs f X x
    have h' := hasDerivAt_integral_orbitWord μ hW' hI' hτ' hτH' Xs f X x
    exact h.unique (h'.congr_of_eventuallyEq (Eventually.of_forall fun t =>
      ih (x * matrixExpUnit n (t • X))))

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

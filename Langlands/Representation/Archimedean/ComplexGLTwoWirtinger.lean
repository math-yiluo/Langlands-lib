import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Wirtinger derivatives on `ℂ`

A real-linear map `L : ℂ → ℂ` is `h ↦ A h + B h̄` with `A = (L 1 - i L i) / 2` and
`B = (L 1 + i L i) / 2` (`clm_eq_wirt`). For a real-differentiable `φ : ℂ → ℂ` these are the
Wirtinger derivatives `∂φ(z) = dz φ z` and `∂̄φ(z) = dzb φ z`. `HasWirt φ A B z` says that `φ`
has the real derivative `h ↦ A h + B h̄` at `z`; it is closed under sums, products, powers and
composition with holomorphic functions, and the weight `pw σ z = (1 + |z|²)^σ` has
`∂ = σ z̄ (1 + |z|²)^(σ-1)` and `∂̄ = σ z (1 + |z|²)^(σ-1)`.
-/

noncomputable section

open Complex ComplexConjugate Filter Topology

namespace Langlands.Archimedean.ComplexGLTwoNoncompact

/-! ## Real-linear maps of `ℂ` -/

/-- The real-linear map `h ↦ A h + B h̄`. -/
def wirt (A B : ℂ) : ℂ →L[ℝ] ℂ :=
  A • ContinuousLinearMap.id ℝ ℂ + B • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp]
theorem wirt_apply (A B h : ℂ) : wirt A B h = A * h + B * conj h := by
  simp [wirt]

theorem wirt_add (A B A' B' : ℂ) : wirt A B + wirt A' B' = wirt (A + A') (B + B') := by
  ext1 h
  simp only [add_apply, wirt_apply]
  ring

theorem wirt_sub (A B A' B' : ℂ) : wirt A B - wirt A' B' = wirt (A - A') (B - B') := by
  ext1 h
  simp only [sub_apply, wirt_apply]
  ring

theorem smul_wirt (c A B : ℂ) : c • wirt A B = wirt (c * A) (c * B) := by
  ext1 h
  simp only [smul_apply, wirt_apply, smul_eq_mul]
  ring

theorem wirt_zero : wirt 0 0 = 0 := by
  ext1 h
  simp

/-- Every real-linear map `L : ℂ → ℂ` is `h ↦ A h + B h̄`. -/
theorem clm_eq_wirt (L : ℂ →L[ℝ] ℂ) :
    L = wirt ((L 1 - I * L I) / 2) ((L 1 + I * L I) / 2) := by
  ext1 h
  have e : h = (h.re : ℝ) • (1 : ℂ) + (h.im : ℝ) • I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im h).symm
  have hL : L h = (h.re : ℂ) * L 1 + (h.im : ℂ) * L I := by
    conv_lhs => rw [e]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hc : conj h = (h.re : ℂ) - (h.im : ℂ) * I := by
    conv_lhs => rw [(Complex.re_add_im h).symm]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hh : h = (h.re : ℂ) + (h.im : ℂ) * I := (Complex.re_add_im h).symm
  rw [hL, wirt_apply, hc]
  set x : ℂ := (h.re : ℂ)
  set y : ℂ := (h.im : ℂ)
  rw [hh]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Wirtinger derivatives -/

/-- The Wirtinger derivative `∂φ(z) = (Dφ(z) 1 - i Dφ(z) i) / 2`. -/
def dz (φ : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ φ z 1 - I * fderiv ℝ φ z I) / 2

/-- The Wirtinger derivative `∂̄φ(z) = (Dφ(z) 1 + i Dφ(z) i) / 2`. -/
def dzb (φ : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ φ z 1 + I * fderiv ℝ φ z I) / 2

theorem fderiv_eq_wirt (φ : ℂ → ℂ) (z : ℂ) : fderiv ℝ φ z = wirt (dz φ z) (dzb φ z) :=
  clm_eq_wirt _

theorem fderiv_apply_eq (φ : ℂ → ℂ) (z h : ℂ) :
    fderiv ℝ φ z h = dz φ z * h + dzb φ z * conj h := by
  rw [fderiv_eq_wirt, wirt_apply]

/-- `φ` has the real derivative `h ↦ A h + B h̄` at `z`. -/
def HasWirt (φ : ℂ → ℂ) (A B z : ℂ) : Prop := HasFDerivAt φ (wirt A B) z

variable {φ ψ : ℂ → ℂ} {A B A' B' z : ℂ}

theorem HasWirt.differentiableAt (h : HasWirt φ A B z) : DifferentiableAt ℝ φ z :=
  HasFDerivAt.differentiableAt h

theorem HasWirt.fderiv (h : HasWirt φ A B z) : fderiv ℝ φ z = wirt A B :=
  HasFDerivAt.fderiv h

theorem HasWirt.dz_eq (h : HasWirt φ A B z) : dz φ z = A := by
  rw [dz, h.fderiv, wirt_apply, wirt_apply]
  simp only [map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem HasWirt.dzb_eq (h : HasWirt φ A B z) : dzb φ z = B := by
  rw [dzb, h.fderiv, wirt_apply, wirt_apply]
  simp only [map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem hasWirt_of_differentiableAt (h : DifferentiableAt ℝ φ z) :
    HasWirt φ (dz φ z) (dzb φ z) z := by
  unfold HasWirt
  rw [← fderiv_eq_wirt]
  exact h.hasFDerivAt

theorem HasWirt.congr_of_eventuallyEq (h : HasWirt φ A B z) (h' : ψ =ᶠ[𝓝 z] φ) :
    HasWirt ψ A B z :=
  HasFDerivAt.congr_of_eventuallyEq h h'

theorem HasWirt.congr (h : HasWirt φ A B z) (hA : A = A') (hB : B = B') : HasWirt φ A' B' z := by
  rw [← hA, ← hB]
  exact h

/-! ## Rules -/

theorem hasWirt_const (c z : ℂ) : HasWirt (fun _ => c) 0 0 z := by
  unfold HasWirt
  rw [wirt_zero]
  exact hasFDerivAt_const c z

theorem hasWirt_id (z : ℂ) : HasWirt (fun x => x) 1 0 z := by
  unfold HasWirt
  have h : wirt 1 0 = ContinuousLinearMap.id ℝ ℂ := by
    ext1 h
    simp
  rw [h]
  exact hasFDerivAt_id z

theorem hasWirt_conj (z : ℂ) : HasWirt (fun x => conj x) 0 1 z := by
  unfold HasWirt
  have h : wirt 0 1 = (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    ext1 h
    simp
  rw [h]
  exact Complex.conjCLE.hasFDerivAt

theorem HasWirt.add (hφ : HasWirt φ A B z) (hψ : HasWirt ψ A' B' z) :
    HasWirt (fun x => φ x + ψ x) (A + A') (B + B') z := by
  unfold HasWirt
  rw [← wirt_add]
  exact HasFDerivAt.add hφ hψ

theorem HasWirt.sub (hφ : HasWirt φ A B z) (hψ : HasWirt ψ A' B' z) :
    HasWirt (fun x => φ x - ψ x) (A - A') (B - B') z := by
  unfold HasWirt
  rw [← wirt_sub]
  exact HasFDerivAt.sub hφ hψ

theorem HasWirt.const_mul (hφ : HasWirt φ A B z) (c : ℂ) :
    HasWirt (fun x => c * φ x) (c * A) (c * B) z := by
  unfold HasWirt
  rw [← smul_wirt]
  exact HasFDerivAt.const_mul hφ c

theorem HasWirt.mul (hφ : HasWirt φ A B z) (hψ : HasWirt ψ A' B' z) :
    HasWirt (fun x => φ x * ψ x) (φ z * A' + ψ z * A) (φ z * B' + ψ z * B) z := by
  unfold HasWirt
  rw [← wirt_add, ← smul_wirt, ← smul_wirt]
  exact HasFDerivAt.mul hφ hψ

theorem HasWirt.pow (hφ : HasWirt φ A B z) (n : ℕ) :
    HasWirt (fun x => φ x ^ n) ((n : ℂ) * φ z ^ (n - 1) * A) ((n : ℂ) * φ z ^ (n - 1) * B) z := by
  unfold HasWirt
  have h := HasFDerivAt.pow hφ n
  rw [nsmul_eq_mul, smul_wirt] at h
  exact h

/-- Composition with a holomorphic function. -/
theorem HasWirt.comp_holo {g : ℂ → ℂ} {g' : ℂ} (hg : HasDerivAt g g' (φ z))
    (hφ : HasWirt φ A B z) : HasWirt (fun x => g (φ x)) (g' * A) (g' * B) z := by
  unfold HasWirt
  rw [← smul_wirt]
  exact hg.comp_hasFDerivAt z hφ

theorem HasWirt.zpow (hφ : HasWirt φ A B z) (hz : φ z ≠ 0) (n : ℤ) :
    HasWirt (fun x => φ x ^ n) ((n : ℂ) * φ z ^ (n - 1) * A) ((n : ℂ) * φ z ^ (n - 1) * B) z := by
  have h := HasWirt.comp_holo (hasDerivAt_zpow n (φ z) (Or.inl hz)) hφ
  exact h.congr (by ring) (by ring)

/-! ## The weight `(1 + |z|²)^σ` -/

/-- `W(z) = 1 + |z|² = 1 + z z̄`. -/
def W (z : ℂ) : ℂ := 1 + z * conj z

theorem W_eq (z : ℂ) : W z = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [W, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem one_add_norm_sq_pos (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity

theorem W_ne_zero (z : ℂ) : W z ≠ 0 := by
  rw [W_eq]
  exact Complex.ofReal_ne_zero.mpr (one_add_norm_sq_pos z).ne'

/-- `(1 + |z|²)^σ`, written as `exp(σ log(1 + |z|²))`. -/
def pw (σ z : ℂ) : ℂ := Complex.exp (σ * (Real.log (1 + ‖z‖ ^ 2) : ℂ))

theorem pw_ne_zero (σ z : ℂ) : pw σ z ≠ 0 := Complex.exp_ne_zero _

theorem pw_add (σ τ z : ℂ) : pw (σ + τ) z = pw σ z * pw τ z := by
  rw [pw, pw, pw, add_mul, Complex.exp_add]

theorem pw_zero (z : ℂ) : pw 0 z = 1 := by
  simp [pw]

theorem pw_one (z : ℂ) : pw 1 z = W z := by
  rw [pw, one_mul, ← Complex.ofReal_exp, Real.exp_log (one_add_norm_sq_pos z), W_eq]

theorem pw_sub_one (σ z : ℂ) : pw (σ - 1) z = pw σ z / W z := by
  have h := pw_add (σ - 1) 1 z
  rw [sub_add_cancel, pw_one] at h
  rw [h, mul_div_cancel_right₀ _ (W_ne_zero z)]

theorem pw_add_one (σ z : ℂ) : pw (σ + 1) z = pw σ z * W z := by
  rw [pw_add, pw_one]

theorem pw_eq_comp (σ z : ℂ) :
    pw σ z = Complex.exp (σ * Complex.log (1 + z * conj z)) := by
  rw [pw, ← W, W_eq, Complex.ofReal_log (one_add_norm_sq_pos z).le]

theorem hasWirt_W (z : ℂ) : HasWirt W (conj z) z z := by
  have h := (hasWirt_const 1 z).add ((hasWirt_id z).mul (hasWirt_conj z))
  refine (h.congr ?_ ?_)
  · simp
  · simp

/-- `∂(1 + |z|²)^σ = σ z̄ (1 + |z|²)^(σ-1)` and `∂̄(1 + |z|²)^σ = σ z (1 + |z|²)^(σ-1)`. -/
theorem hasWirt_pw (σ z : ℂ) :
    HasWirt (pw σ) (σ * conj z * pw (σ - 1) z) (σ * z * pw (σ - 1) z) z := by
  have hslit : 1 + z * conj z ∈ Complex.slitPlane := by
    rw [← W, W_eq]
    exact Complex.ofReal_mem_slitPlane.mpr (one_add_norm_sq_pos z)
  have hg : HasDerivAt (fun u : ℂ => Complex.exp (σ * Complex.log u))
      (Complex.exp (σ * Complex.log (W z)) * (σ * (W z)⁻¹)) (W z) := by
    have h1 := ((Complex.hasDerivAt_log (hslit)).const_mul σ).cexp
    exact h1
  have h := HasWirt.comp_holo hg (hasWirt_W z)
  have hfun : (fun x => Complex.exp (σ * Complex.log (W x))) = pw σ := by
    funext x
    rw [pw_eq_comp, W]
  rw [hfun] at h
  refine h.congr ?_ ?_
  · rw [pw_sub_one, pw_eq_comp, W]
    field_simp
  · rw [pw_sub_one, pw_eq_comp, W]
    field_simp

end Langlands.Archimedean.ComplexGLTwoNoncompact

import Langlands.Representation.Archimedean.ComplexGLTwoPolynomial
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-!
# Functions of the bottom row on `GL_2(ℂ)` and their right derivatives

For a function `Φ` on `ℂ`, a complex exponent `s` and a polynomial `P` in `r, r̄`,
`realize Φ s P M = Φ (det M) · |r|^(2s) · P(r, r̄)` where `r` is the bottom row of the matrix
`M` and `|r|^(2s) = (|r|²)^s`. For a traceless direction `X`, the right derivative of such a
function is again of this form, with exponent `s - 1` and the polynomial
`s · L_X · P + N · T_X P` (`rightDerivative_realize`): `L_X` is the derivative of `N = |r|²`
along `r ↦ r X` and `T_X` the derivative of `P` along `r ↦ r X`.
-/

noncomputable section

open MvPolynomial
open scoped Manifold ContDiff Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.GLTwoModel

open GLTwoPoly

/-! ## Derivatives of polynomials along curves -/

theorem hasDerivAt_eval_curve {x : ℝ → Var → ℂ} {x' : Var → ℂ} {t₀ : ℝ}
    (hx : ∀ i, HasDerivAt (fun t => x t i) (x' i) t₀) (P : Pol) :
    HasDerivAt (fun t => eval (x t) P) (∑ i, x' i * eval (x t₀) (pderiv i P)) t₀ := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t₀ a
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p n hp =>
    have key : ∀ i, x' i * eval (x t₀) (pderiv i (p * X n)) =
        x t₀ n * (x' i * eval (x t₀) (pderiv i p)) +
          if i = n then x' i * eval (x t₀) p else 0 := by
      intro i
      rw [pderiv_mul, pderiv_X]
      by_cases h : i = n
      · subst h; simp; ring
      · simp [Pi.single_apply, Ne.symm h, h]; ring
    rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _), ← Finset.mul_sum]
    simp only [map_mul, eval_X]
    convert hp.mul (hx n) using 1
    ring

/-- Evaluation at `(r, r̄)` of a polynomial along the real line `r + t v`. -/
theorem hasDerivAt_ev_line (r v : Fin 2 → ℂ) (P : Pol) :
    HasDerivAt (fun t : ℝ => ev (r + (t : ℂ) • v) P)
      (∑ k, (v k * ev r (dz k P) + starRingEnd ℂ (v k) * ev r (dw k P))) 0 := by
  have hx : ∀ i : Var, HasDerivAt
      (fun t : ℝ => (Sum.elim (r + (t : ℂ) • v) fun k => starRingEnd ℂ ((r + (t : ℂ) • v) k)) i)
      ((Sum.elim v fun k => starRingEnd ℂ (v k)) i) 0 := by
    intro i
    rcases i with k | k
    · simp only [Sum.elim_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (v k)).const_add (r k)
    · simp only [Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
        Complex.conj_ofReal]
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
        (starRingEnd ℂ (v k))).const_add (starRingEnd ℂ (r k))
  have h := hasDerivAt_eval_curve hx P
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero, zero_smul,
    add_zero] at h
  rw [Finset.sum_add_distrib]
  exact h

/-! ## The bottom row and the realization -/

/-- The bottom row of a `2 × 2` matrix. -/
def row (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → ℂ := fun k => M 1 k

/-- `|r|² = |r_0|² + |r_1|²`. -/
def nrm (r : Fin 2 → ℂ) : ℝ := ‖r 0‖ ^ 2 + ‖r 1‖ ^ 2

theorem ev_z (r : Fin 2 → ℂ) (k : Fin 2) : ev r (z k) = r k := by simp [ev, z]

theorem ev_w (r : Fin 2 → ℂ) (k : Fin 2) : ev r (w k) = starRingEnd ℂ (r k) := by simp [ev, w]

theorem ev_C (r : Fin 2 → ℂ) (c : ℂ) : ev r (C c) = c := by simp [ev]

theorem ev_add (r : Fin 2 → ℂ) (P Q : Pol) : ev r (P + Q) = ev r P + ev r Q := by simp [ev]

theorem ev_sub (r : Fin 2 → ℂ) (P Q : Pol) : ev r (P - Q) = ev r P - ev r Q := by simp [ev]

theorem ev_mul (r : Fin 2 → ℂ) (P Q : Pol) : ev r (P * Q) = ev r P * ev r Q := by simp [ev]

theorem ev_sum (r : Fin 2 → ℂ) (f : Fin 2 → Pol) : ev r (∑ k, f k) = ∑ k, ev r (f k) := by
  simp [ev]

theorem ev_N (r : Fin 2 → ℂ) : ev r N = (nrm r : ℂ) := by
  simp only [N, ev_add, ev_mul, ev_z, ev_w, nrm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem nrm_pos_of_det_ne_zero {M : Matrix (Fin 2) (Fin 2) ℂ} (h : M.det ≠ 0) :
    0 < nrm (row M) := by
  by_contra hle
  push Not at hle
  have h0 : ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2 ≤ 0 := hle
  have e0 : M 1 0 = 0 := by
    have := sq_nonneg ‖M 1 1‖
    have : ‖M 1 0‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    simpa using this
  have e1 : M 1 1 = 0 := by
    have := sq_nonneg ‖M 1 0‖
    have : ‖M 1 1‖ ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    simpa using this
  apply h
  rw [Matrix.det_fin_two, e0, e1]
  ring

/-- `Φ(det M) · (|r|²)^s · P(r, r̄)` with `r` the bottom row of `M`. -/
def realize (Φ : ℂ → ℂ) (s : ℂ) (P : Pol) (M : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Φ M.det * (nrm (row M) : ℂ) ^ s * ev (row M) P

theorem realize_add (Φ : ℂ → ℂ) (s : ℂ) (P Q : Pol) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    realize Φ s (P + Q) M = realize Φ s P M + realize Φ s Q M := by
  simp only [realize, ev_add]; ring

theorem realize_sub (Φ : ℂ → ℂ) (s : ℂ) (P Q : Pol) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    realize Φ s (P - Q) M = realize Φ s P M - realize Φ s Q M := by
  simp only [realize, ev_sub]; ring

theorem realize_C_mul (Φ : ℂ → ℂ) (s c : ℂ) (P : Pol) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    realize Φ s (C c * P) M = c * realize Φ s P M := by
  simp only [realize, ev_mul, ev_C]; ring

theorem realize_zero (Φ : ℂ → ℂ) (s : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    realize Φ s 0 M = 0 := by
  simp [realize, ev]

theorem realize_N_mul (Φ : ℂ → ℂ) (s : ℂ) (P : Pol) {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.det ≠ 0) : realize Φ s (N * P) M = realize Φ (s + 1) P M := by
  have hne : (nrm (row M) : ℂ) ≠ 0 := by
    exact_mod_cast (nrm_pos_of_det_ne_zero hM).ne'
  simp only [realize, ev_mul, ev_N, Complex.cpow_add _ _ hne, Complex.cpow_one]
  ring

/-! ## The polynomials of a right derivative -/

/-- `(z X)_k = Σ_i X_{ik} z_i`: the `k`-th coordinate of `r X`. -/
def zX (X : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 2) : Pol := ∑ i, C (X i k) * z i

/-- `(w X̄)_k = Σ_i conj(X_{ik}) w_i`: the `k`-th coordinate of `conj(r X)`. -/
def wX (X : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 2) : Pol :=
  ∑ i, C (starRingEnd ℂ (X i k)) * w i

/-- The derivative of `N` along `r ↦ r X`. -/
def Lpol (X : Matrix (Fin 2) (Fin 2) ℂ) : Pol := ∑ k, (w k * zX X k + z k * wX X k)

/-- The derivative of `P` along `r ↦ r X`. -/
def Tpol (X : Matrix (Fin 2) (Fin 2) ℂ) (P : Pol) : Pol :=
  ∑ k, (zX X k * dz k P + wX X k * dw k P)

/-- The polynomial `s L_X P + N T_X P` of the right derivative along `X` (at exponent
`s - 1`). -/
def stepPol (X : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (P : Pol) : Pol :=
  C s * (Lpol X * P) + N * Tpol X P

theorem ev_zX (r : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 2) :
    ev r (zX X k) = Matrix.vecMul r X k := by
  simp only [zX, ev_sum, ev_mul, ev_C, ev_z, Matrix.vecMul, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem ev_wX (r : Fin 2 → ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 2) :
    ev r (wX X k) = starRingEnd ℂ (Matrix.vecMul r X k) := by
  simp only [wX, ev_sum, ev_mul, ev_C, ev_w, Matrix.vecMul, dotProduct, map_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## The right derivative -/

theorem row_line (M X : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    row (M + t • (M * X)) = row M + (t : ℂ) • Matrix.vecMul (row M) X := by
  funext k
  simp [row, Matrix.mul_apply, Matrix.vecMul, dotProduct, Complex.real_smul]

theorem det_line (M X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0) (t : ℝ) :
    (M + t • (M * X)).det = M.det * (1 + ((t ^ 2 : ℝ) : ℂ) * X.det) := by
  have e : M + t • (M * X) = M * (1 + t • X) := by
    rw [mul_add, mul_one, Matrix.mul_smul]
  rw [e, Matrix.det_mul]
  congr 1
  rw [Matrix.trace_fin_two] at hX
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    Complex.real_smul]
  simp
  linear_combination (t : ℂ) * hX

theorem hasDerivAt_det_line (M X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableAt ℝ Φ M.det) :
    HasDerivAt (fun t : ℝ => Φ (M + t • (M * X)).det) 0 0 := by
  simp_rw [det_line M X hX]
  have h1 : HasDerivAt (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).ofReal_comp
  have hc : HasDerivAt (fun t : ℝ => M.det * (1 + ((t ^ 2 : ℝ) : ℂ) * X.det)) 0 0 := by
    simpa using ((h1.mul_const X.det).const_add 1).const_mul M.det
  have := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hΦ.hasFDerivAt hc (by simp)
  rw [map_zero] at this
  exact this

theorem hasDerivAt_realize_line {Φ : ℂ → ℂ} (s : ℂ) (P : Pol) (M X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.trace = 0) (hM : M.det ≠ 0) (hΦ : DifferentiableAt ℝ Φ M.det) :
    HasDerivAt (fun t : ℝ => realize Φ s P (M + t • (M * X)))
      (realize Φ (s - 1) (stepPol X s P) M) 0 := by
  set r := row M with hr
  set v := Matrix.vecMul r X with hv
  have hrow : ∀ t : ℝ, row (M + t • (M * X)) = r + (t : ℂ) • v := row_line M X
  simp only [realize, hrow]
  have hpos := nrm_pos_of_det_ne_zero hM
  have hNline : HasDerivAt (fun t : ℝ => (nrm (r + (t : ℂ) • v) : ℂ))
      (∑ k, (v k * starRingEnd ℂ (r k) + starRingEnd ℂ (v k) * r k)) 0 := by
    have h := hasDerivAt_ev_line r v N
    simp only [dz_N, dw_N, ev_z, ev_w, ev_N] at h
    exact h
  have hcp : HasDerivAt (fun z : ℂ => z ^ s) (s * (nrm r : ℂ) ^ (s - 1)) (nrm r : ℂ) :=
    (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hpos)).hasDerivAt
  have hh0 : (fun t : ℝ => (nrm (r + (t : ℂ) • v) : ℂ)) 0 = (nrm r : ℂ) := by simp
  rw [← hh0] at hcp
  have hNs := HasDerivAt.comp (h := fun t : ℝ => (nrm (r + (t : ℂ) • v) : ℂ))
    (h₂ := fun z : ℂ => z ^ s) (0 : ℝ) hcp hNline
  have hP := hasDerivAt_ev_line r v P
  have hD := hasDerivAt_det_line M X hX hΦ
  have hprod := (hD.mul hNs).mul hP
  refine hprod.congr_deriv ?_
  have hne : (nrm r : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hpow : (nrm r : ℂ) ^ s = (nrm r : ℂ) ^ (s - 1) * (nrm r : ℂ) := by
    conv_lhs => rw [show s = (s - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
  simp only [Complex.ofReal_zero, zero_smul, add_zero, zero_mul, zero_add, stepPol, ev_add,
    ev_mul, ev_C, ev_N, Lpol, Tpol, ev_sum, ev_z, ev_w, ev_zX, ev_wX, Pi.mul_apply,
    Function.comp_apply, ← hr, ← hv]
  rw [hpow]
  simp only [Fin.sum_univ_two]
  ring

/-- **Right derivatives of bottom-row functions.** If a smooth function `f` on `GL_2(ℂ)` is
`realize Φ s P`, with `Φ` real differentiable at `det g`, then for traceless `X` its right
derivative along `X` at `g` is `realize Φ (s - 1) (stepPol X s P)` at `g`. -/
theorem rightDerivative_realize {Φ : ℂ → ℂ} {s : ℂ} {P : Pol}
    {f : Langlands.GeneralLinear 2 ℂ → ℂ} (hf : ContMDiff (matrixModel ℂ 2) 𝓘(ℝ, ℂ) ∞ f)
    (hfe : ∀ g : Langlands.GeneralLinear 2 ℂ, f g = realize Φ s P g)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (hX : X.trace = 0) (g : Langlands.GeneralLinear 2 ℂ)
    (hΦ : DifferentiableAt ℝ Φ (g : Matrix (Fin 2) (Fin 2) ℂ).det) :
    rightDerivative (matrixModel ℂ 2) X f g = realize Φ (s - 1) (stepPol X s P) g := by
  rw [rightDerivative_eq_fderiv hf]
  set M : Matrix (Fin 2) (Fin 2) ℂ := (g : Matrix (Fin 2) (Fin 2) ℂ) with hMg
  have hM : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit g) |>.ne_zero
  set γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => M + t • (M * X) with hγ
  have hγd : HasDerivAt γ (M * X) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (M * X)).const_add M
    rw [one_smul] at this
    exact this
  have hF := (differentiableAt_unitsExtension hf (Units.isUnit g)).hasFDerivAt
  have h1 : HasDerivAt (unitsExtension f ∘ γ) (fderiv ℝ (unitsExtension f) M (M * X)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hF hγd (by simp [γ, M])
  have hev : (fun t => realize Φ s P (γ t)) =ᶠ[nhds (0 : ℝ)] (unitsExtension f ∘ γ) := by
    have hcont : Continuous γ := by
      simp only [γ]; fun_prop
    have hopen := isOpen_setOf_isUnit_matrix.preimage hcont
    have hmem : (0 : ℝ) ∈ γ ⁻¹' {y : Matrix (Fin 2) (Fin 2) ℂ | IsUnit y} := by
      simp [γ, M, Units.isUnit]
    filter_upwards [hopen.mem_nhds hmem] with t ht
    obtain ⟨u, hu⟩ := ht
    simp only [Function.comp_apply]
    rw [← hu, unitsExtension_val, hfe]
  have h2 := (hasDerivAt_realize_line s P M X hX hM hΦ).congr_of_eventuallyEq hev.symm
  exact h1.unique h2

/-! ## The complexified Lie algebra action on realized functions -/

/-- `f` agrees with `realize Φ s P` on `GL_2(ℂ)`. -/
def IsRealized (Φ : ℂ → ℂ) (s : ℂ) (P : Pol) (f : Langlands.GeneralLinear 2 ℂ → ℂ) : Prop :=
  ∀ g : Langlands.GeneralLinear 2 ℂ, f g = realize Φ s P (g : Matrix (Fin 2) (Fin 2) ℂ)

theorem det_ne_zero (g : Langlands.GeneralLinear 2 ℂ) :
    (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero

theorem IsRealized.N_mul {Φ : ℂ → ℂ} {s : ℂ} {P : Pol} {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (h : IsRealized Φ (s + 1) P f) : IsRealized Φ s (N * P) f := fun g => by
  rw [h g, realize_N_mul _ _ _ (det_ne_zero g)]

theorem IsRealized.of_N_mul {Φ : ℂ → ℂ} {s : ℂ} {P : Pol} {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (h : IsRealized Φ s (N * P) f) : IsRealized Φ (s + 1) P f := fun g => by
  rw [h g, realize_N_mul _ _ _ (det_ne_zero g)]

theorem IsRealized.congr_exp {Φ : ℂ → ℂ} {s s' : ℂ} {P : Pol}
    {f : Langlands.GeneralLinear 2 ℂ → ℂ} (h : IsRealized Φ s P f) (hs : s = s') :
    IsRealized Φ s' P f := hs ▸ h

/-- The matrix `!![r̄₁, -r̄₀; r₀, r₁]` with bottom row `r` and determinant `|r|²`. -/
def bottomMat (r : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![starRingEnd ℂ (r 1), -starRingEnd ℂ (r 0); r 0, r 1]

theorem det_bottomMat (r : Fin 2 → ℂ) : (bottomMat r).det = (nrm r : ℂ) := by
  rw [bottomMat, Matrix.det_fin_two_of, ← ev_N]
  simp only [N, ev_add, ev_mul, ev_z, ev_w]
  ring

theorem row_bottomMat (r : Fin 2 → ℂ) : row (bottomMat r) = r := by
  funext k; fin_cases k <;> rfl

theorem nrm_pos_of_ne_zero {r : Fin 2 → ℂ} (hr : r ≠ 0) : 0 < nrm r := by
  have h : (bottomMat r).det ≠ 0 := by
    rw [det_bottomMat]
    intro h0
    have h0' : ‖r 0‖ ^ 2 + ‖r 1‖ ^ 2 = 0 := by exact_mod_cast h0
    apply hr
    funext k
    have a0 : ‖r 0‖ = 0 := by nlinarith [sq_nonneg ‖r 0‖, sq_nonneg ‖r 1‖, norm_nonneg (r 0)]
    have a1 : ‖r 1‖ = 0 := by nlinarith [sq_nonneg ‖r 0‖, sq_nonneg ‖r 1‖, norm_nonneg (r 1)]
    fin_cases k
    · simpa using a0
    · simpa using a1
  have := nrm_pos_of_det_ne_zero h
  rwa [row_bottomMat] at this

/-- **Injectivity of the realization.** If `Φ` does not vanish on `ℂˣ`, a polynomial whose
realization vanishes on `GL_2(ℂ)` is zero. -/
theorem eq_zero_of_isRealized_zero {Φ : ℂ → ℂ} (hΦ0 : ∀ δ : ℂ, δ ≠ 0 → Φ δ ≠ 0) {s : ℂ}
    {Q : Pol} (h : IsRealized Φ s Q 0) : Q = 0 := by
  refine eq_zero_of_ev Q fun r hr => ?_
  have hpos := nrm_pos_of_ne_zero hr
  have hdet : (bottomMat r).det ≠ 0 := by
    rw [det_bottomMat]; exact_mod_cast hpos.ne'
  have hu : IsUnit (bottomMat r) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet)
  have h1 := h hu.unit
  rw [Pi.zero_apply, IsUnit.unit_spec, realize, row_bottomMat] at h1
  have hN : (nrm r : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne')]
    exact Complex.exp_ne_zero _
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (hΦ0 _ hdet)
    · exact absurd h3 hN
  · exact h2

theorem IsRealized.unique {Φ : ℂ → ℂ} {s : ℂ} {P : Pol} {f f' : Langlands.GeneralLinear 2 ℂ → ℂ}
    (h : IsRealized Φ s P f) (h' : IsRealized Φ s P f') : f = f' := by
  funext g
  rw [h g, h' g]

theorem IsRealized.add {Φ : ℂ → ℂ} {s : ℂ} {P Q : Pol} {f f' : Langlands.GeneralLinear 2 ℂ → ℂ}
    (h : IsRealized Φ s P f) (h' : IsRealized Φ s Q f') : IsRealized Φ s (P + Q) (f + f') :=
  fun g => by rw [Pi.add_apply, h g, h' g, realize_add]

theorem IsRealized.sub {Φ : ℂ → ℂ} {s : ℂ} {P Q : Pol} {f f' : Langlands.GeneralLinear 2 ℂ → ℂ}
    (h : IsRealized Φ s P f) (h' : IsRealized Φ s Q f') : IsRealized Φ s (P - Q) (f - f') :=
  fun g => by rw [Pi.sub_apply, h g, h' g, realize_sub]

theorem IsRealized.smul {Φ : ℂ → ℂ} {s : ℂ} {P : Pol} {f : Langlands.GeneralLinear 2 ℂ → ℂ}
    (h : IsRealized Φ s P f) (c : ℂ) : IsRealized Φ s (C c * P) (c • f) :=
  fun g => by rw [Pi.smul_apply, h g, realize_C_mul, smul_eq_mul]

theorem isRealized_zero (Φ : ℂ → ℂ) (s : ℂ) : IsRealized Φ s 0 0 :=
  fun g => by rw [Pi.zero_apply, realize_zero]

variable (ds : List LocalFactor.Archimedean.ComplexCharacterData)

/-- The `U(2)`-finite functions of the standard module of `ds`. -/
abbrev KF2 := kFiniteFunctions (complexStandardModule 2 ds) (unitaryCompact ℂ 2)

theorem coe_lie_tmul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) (x : KF2 ds) :
    ((complexStandardLie 2 ds (c ⊗ₜ[ℝ] X) x : KF2 ds) : Langlands.GeneralLinear 2 ℂ → ℂ) =
      c • rightDerivative (matrixModel ℂ 2) X (x : Langlands.GeneralLinear 2 ℂ → ℂ) := by
  rw [complexStandardLie, principalSeriesLie, kFiniteLie_tmul, LinearMap.smul_apply,
    Submodule.coe_smul, kFiniteDerivative_apply_coe]

variable {ds}

theorem smooth_of_mem (x : KF2 ds) :
    ContMDiff (matrixModel ℂ 2) 𝓘(ℝ, ℂ) ∞ (x : Langlands.GeneralLinear 2 ℂ → ℂ) :=
  x.2.1.1

/-- The action of `c₁ ⊗ X₁ + c₂ ⊗ X₂` (traceless `X₁`, `X₂`) on a realized function. -/
theorem isRealized_lie_two {Φ : ℂ → ℂ} (hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ)
    {s : ℂ} {P : Pol} {x : KF2 ds} (hx : IsRealized Φ s P x) (c₁ c₂ : ℂ)
    (X₁ X₂ : Matrix (Fin 2) (Fin 2) ℂ) (h₁ : X₁.trace = 0) (h₂ : X₂.trace = 0) :
    IsRealized Φ (s - 1) (C c₁ * stepPol X₁ s P + C c₂ * stepPol X₂ s P)
      (complexStandardLie 2 ds (c₁ ⊗ₜ[ℝ] X₁ + c₂ ⊗ₜ[ℝ] X₂) x) := by
  intro g
  rw [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, coe_lie_tmul, coe_lie_tmul,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    rightDerivative_realize (smooth_of_mem x) hx X₁ h₁ g (hΦ _ (det_ne_zero g)),
    rightDerivative_realize (smooth_of_mem x) hx X₂ h₂ g (hΦ _ (det_ne_zero g)),
    realize_add, realize_C_mul, realize_C_mul]

/-! ## Holomorphic and antiholomorphic moves -/

open Complex in
/-- `E^h(X) = ½ (X - i (i X))`, acting as the holomorphic vector field of `r ↦ r X`. -/
def hol (X : Matrix (Fin 2) (Fin 2) ℂ) : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) ⊗ₜ X + (-(I / 2)) ⊗ₜ (I • X)

open Complex in
/-- `E^a(X) = ½ (X + i (i X))`, acting as the antiholomorphic vector field of `r ↦ r X`. -/
def antihol (X : Matrix (Fin 2) (Fin 2) ℂ) : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) ⊗ₜ X + (I / 2) ⊗ₜ (I • X)

/-- `Σ_l w_l (z X)_l`. -/
def holZ (X : Matrix (Fin 2) (Fin 2) ℂ) : Pol := ∑ l, w l * zX X l

/-- `Σ_l (z X)_l ∂_{z_l}`. -/
def holT (X : Matrix (Fin 2) (Fin 2) ℂ) (P : Pol) : Pol := ∑ l, zX X l * dz l P

/-- `Σ_l z_l (w X̄)_l`. -/
def antiZ (X : Matrix (Fin 2) (Fin 2) ℂ) : Pol := ∑ l, z l * wX X l

/-- `Σ_l (w X̄)_l ∂_{w_l}`. -/
def antiT (X : Matrix (Fin 2) (Fin 2) ℂ) (P : Pol) : Pol := ∑ l, wX X l * dw l P

theorem zX_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) (l : Fin 2) :
    zX (c • X) l = C c * zX X l := by
  simp only [zX, Matrix.smul_apply, smul_eq_mul, map_mul, Fin.sum_univ_two]
  ring

theorem wX_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) (l : Fin 2) :
    wX (c • X) l = C (starRingEnd ℂ c) * wX X l := by
  simp only [wX, Matrix.smul_apply, smul_eq_mul, map_mul, Fin.sum_univ_two]
  ring

theorem trace_I_smul {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.trace = 0) :
    (Complex.I • X).trace = 0 := by
  rw [Matrix.trace_smul, hX, smul_zero]

theorem stepPol_eq (X : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (P : Pol) :
    stepPol X s P = C s * ((holZ X + antiZ X) * P) + N * (holT X P + antiT X P) := by
  simp only [stepPol, Lpol, Tpol, holZ, antiZ, holT, antiT, ← Finset.sum_add_distrib]

theorem stepPol_I_smul (X : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (P : Pol) :
    stepPol (Complex.I • X) s P = C s * ((C Complex.I * holZ X - C Complex.I * antiZ X) * P) +
      N * (C Complex.I * holT X P - C Complex.I * antiT X P) := by
  simp only [stepPol, Lpol, Tpol, holZ, antiZ, holT, antiT, zX_smul, wX_smul, Complex.conj_I,
    map_neg, Fin.sum_univ_two]
  ring

theorem isRealized_hol {Φ : ℂ → ℂ} (hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ)
    {s : ℂ} {P : Pol} {x : KF2 ds} (hx : IsRealized Φ s P x) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.trace = 0) :
    IsRealized Φ (s - 1) (C s * (holZ X * P) + N * holT X P)
      (complexStandardLie 2 ds (hol X) x) := by
  have h := isRealized_lie_two hΦ hx (1 / 2) (-(Complex.I / 2)) X (Complex.I • X) hX
    (trace_I_smul hX)
  have e : C (1 / 2 : ℂ) * stepPol X s P + C (-(Complex.I / 2)) * stepPol (Complex.I • X) s P =
      C s * (holZ X * P) + N * holT X P := by
    rw [stepPol_eq, stepPol_I_smul]
    have e1 : (C (1 / 2 : ℂ) : Pol) + C (-(Complex.I / 2)) * C Complex.I = 1 := by
      rw [← map_mul, ← map_add, ← map_one C]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    have e2 : (C (1 / 2 : ℂ) : Pol) - C (-(Complex.I / 2)) * C Complex.I = 0 := by
      rw [← map_mul, ← map_sub, ← map_zero C]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    linear_combination (C s * (holZ X * P) + N * holT X P) * e1 +
      (C s * (antiZ X * P) + N * antiT X P) * e2
  rw [hol]
  intro g
  rw [h g, e]

theorem isRealized_antihol {Φ : ℂ → ℂ} (hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ)
    {s : ℂ} {P : Pol} {x : KF2 ds} (hx : IsRealized Φ s P x) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : X.trace = 0) :
    IsRealized Φ (s - 1) (C s * (antiZ X * P) + N * antiT X P)
      (complexStandardLie 2 ds (antihol X) x) := by
  have h := isRealized_lie_two hΦ hx (1 / 2) (Complex.I / 2) X (Complex.I • X) hX
    (trace_I_smul hX)
  have e : C (1 / 2 : ℂ) * stepPol X s P + C (Complex.I / 2) * stepPol (Complex.I • X) s P =
      C s * (antiZ X * P) + N * antiT X P := by
    rw [stepPol_eq, stepPol_I_smul]
    have e1 : (C (1 / 2 : ℂ) : Pol) + C (Complex.I / 2) * C Complex.I = 0 := by
      rw [← map_mul, ← map_add, ← map_zero C]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    have e2 : (C (1 / 2 : ℂ) : Pol) - C (Complex.I / 2) * C Complex.I = 1 := by
      rw [← map_mul, ← map_sub, ← map_one C]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    linear_combination (C s * (holZ X * P) + N * holT X P) * e1 +
      (C s * (antiZ X * P) + N * antiT X P) * e2
  rw [antihol]
  intro g
  rw [h g, e]

/-! ## The moves of the irreducibility proof -/

/-- `E₀₁`. -/
def E01 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 1 1

/-- `E₁₀`. -/
def E10 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 1 0 1

/-- `E₀₀ - E₁₁`. -/
def Ed : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single 0 0 1 - Matrix.single 1 1 1

theorem trace_E01 : E01.trace = 0 := by simp [E01]
theorem trace_E10 : E10.trace = 0 := by simp [E10]
theorem trace_Ed : Ed.trace = 0 := by simp [Ed]

theorem holZ_E01 : holZ E01 = w 1 * z 0 := by
  simp [holZ, zX, E01, Fin.sum_univ_two, Matrix.single_apply]
theorem holT_E01 (P : Pol) : holT E01 P = z 0 * dz 1 P := by
  simp [holT, zX, E01, Fin.sum_univ_two, Matrix.single_apply]
theorem antiZ_E01 : antiZ E01 = z 1 * w 0 := by
  simp [antiZ, wX, E01, Fin.sum_univ_two, Matrix.single_apply]
theorem antiT_E01 (P : Pol) : antiT E01 P = w 0 * dw 1 P := by
  simp [antiT, wX, E01, Fin.sum_univ_two, Matrix.single_apply]
theorem holZ_E10 : holZ E10 = w 0 * z 1 := by
  simp [holZ, zX, E10, Fin.sum_univ_two, Matrix.single_apply]
theorem holT_E10 (P : Pol) : holT E10 P = z 1 * dz 0 P := by
  simp [holT, zX, E10, Fin.sum_univ_two, Matrix.single_apply]
theorem antiZ_E10 : antiZ E10 = z 0 * w 1 := by
  simp [antiZ, wX, E10, Fin.sum_univ_two, Matrix.single_apply]
theorem antiT_E10 (P : Pol) : antiT E10 P = w 1 * dw 0 P := by
  simp [antiT, wX, E10, Fin.sum_univ_two, Matrix.single_apply]
theorem holZ_Ed : holZ Ed = w 0 * z 0 - w 1 * z 1 := by
  simp [holZ, zX, Ed, Fin.sum_univ_two, Matrix.single_apply]; ring
theorem holT_Ed (P : Pol) : holT Ed P = z 0 * dz 0 P - z 1 * dz 1 P := by
  simp [holT, zX, Ed, Fin.sum_univ_two, Matrix.single_apply]; ring
theorem antiZ_Ed : antiZ Ed = z 0 * w 0 - z 1 * w 1 := by
  simp [antiZ, wX, Ed, Fin.sum_univ_two, Matrix.single_apply]; ring
theorem antiT_Ed (P : Pol) : antiT Ed P = w 0 * dw 0 P - w 1 * dw 1 P := by
  simp [antiT, wX, Ed, Fin.sum_univ_two, Matrix.single_apply]; ring

/-- `X₀₁ = E^h(E₀₁) - E^a(E₁₀)`, acting as `D 0 1`. -/
def k01 : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ := hol E01 - antihol E10

/-- `X₁₀ = E^h(E₁₀) - E^a(E₀₁)`, acting as `D 1 0`. -/
def k10 : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ := hol E10 - antihol E01

/-- `X₀₀ - X₁₁ = E^h(E₀₀ - E₁₁) - E^a(E₀₀ - E₁₁)`, acting as `D 0 0 - D 1 1`. -/
def kd : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ := hol Ed - antihol Ed

theorem IsRealized.sub_lie {Φ : ℂ → ℂ} {s : ℂ} {P Q : Pol} {x : KF2 ds} {a b : ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ}
    (ha : IsRealized Φ s P (complexStandardLie 2 ds a x))
    (hb : IsRealized Φ s Q (complexStandardLie 2 ds b x)) :
    IsRealized Φ s (P - Q) (complexStandardLie 2 ds (a - b) x) := by
  intro g
  rw [map_sub, LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, ha g, hb g, realize_sub]

theorem isRealized_k01 {Φ : ℂ → ℂ} (hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ)
    {s : ℂ} {P : Pol} {x : KF2 ds} (hx : IsRealized Φ s P x) :
    IsRealized Φ s (D 0 1 P) (complexStandardLie 2 ds k01 x) := by
  have h := (isRealized_hol hΦ hx E01 trace_E01).sub_lie (isRealized_antihol hΦ hx E10 trace_E10)
  have e : C s * (holZ E01 * P) + N * holT E01 P - (C s * (antiZ E10 * P) + N * antiT E10 P) =
      N * D 0 1 P := by
    rw [holZ_E01, holT_E01, antiZ_E10, antiT_E10, D]; ring
  rw [e] at h
  exact (h.of_N_mul).congr_exp (by ring)

theorem isRealized_k10 {Φ : ℂ → ℂ} (hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ)
    {s : ℂ} {P : Pol} {x : KF2 ds} (hx : IsRealized Φ s P x) :
    IsRealized Φ s (D 1 0 P) (complexStandardLie 2 ds k10 x) := by
  have h := (isRealized_hol hΦ hx E10 trace_E10).sub_lie (isRealized_antihol hΦ hx E01 trace_E01)
  have e : C s * (holZ E10 * P) + N * holT E10 P - (C s * (antiZ E01 * P) + N * antiT E01 P) =
      N * D 1 0 P := by
    rw [holZ_E10, holT_E10, antiZ_E01, antiT_E01, D]; ring
  rw [e] at h
  exact (h.of_N_mul).congr_exp (by ring)

theorem isRealized_kd {Φ : ℂ → ℂ} (hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ)
    {s : ℂ} {P : Pol} {x : KF2 ds} (hx : IsRealized Φ s P x) :
    IsRealized Φ s (D 0 0 P - D 1 1 P) (complexStandardLie 2 ds kd x) := by
  have h := (isRealized_hol hΦ hx Ed trace_Ed).sub_lie (isRealized_antihol hΦ hx Ed trace_Ed)
  have e : C s * (holZ Ed * P) + N * holT Ed P - (C s * (antiZ Ed * P) + N * antiT Ed P) =
      N * (D 0 0 P - D 1 1 P) := by
    rw [holZ_Ed, holT_Ed, antiZ_Ed, antiT_Ed, D, D]; ring
  rw [e] at h
  exact (h.of_N_mul).congr_exp (by ring)

variable (ds) in
/-- Twice the Casimir operator of `𝔰𝔩_2`: `2 (X₀₁ X₁₀ + X₁₀ X₀₁) + (X₀₀ - X₁₁)²`. -/
def casOp : Module.End ℂ (KF2 ds) :=
  2 • (complexStandardLie 2 ds k01 * complexStandardLie 2 ds k10) +
    2 • (complexStandardLie 2 ds k10 * complexStandardLie 2 ds k01) +
    complexStandardLie 2 ds kd * complexStandardLie 2 ds kd

theorem isRealized_casOp {Φ : ℂ → ℂ} (hΦ : ∀ δ : ℂ, δ ≠ 0 → DifferentiableAt ℝ Φ δ)
    {s : ℂ} {P : Pol} {x : KF2 ds} (hx : IsRealized Φ s P x) :
    IsRealized Φ s (Cas P) (casOp ds x) := by
  have h1 := isRealized_k01 hΦ (isRealized_k10 hΦ hx)
  have h2 := isRealized_k10 hΦ (isRealized_k01 hΦ hx)
  have h3 := isRealized_kd hΦ (isRealized_kd hΦ hx)
  intro g
  simp only [casOp, two_smul, LinearMap.add_apply, Module.End.mul_apply, Submodule.coe_add,
    Pi.add_apply, h1 g, h2 g, h3 g]
  rw [Cas, two_mul, two_mul, realize_add, realize_add, realize_add, realize_add]

end Langlands.Archimedean.GLTwoModel

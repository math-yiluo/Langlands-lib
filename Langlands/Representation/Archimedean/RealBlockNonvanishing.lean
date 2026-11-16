import Langlands.Representation.Archimedean.RealBlockFunctional

/-!
# Nonvanishing of the block Jacquet functional on `GL_n(ℝ)`

The block Jacquet functional `RealBlockFunctional.jac` is nonzero on the `O(n)`-finite principal
series: some test vector (a sign monomial times powers of squared lower-right minors, extended to
the principal series) has nonzero `jac`. The proof concentrates the partial Jacquet integral of each
block at `X = 0` by an approximate identity on `M_{(k+1)×a}(ℝ)`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealBlockNonvanishing

open RealBlockParabolic RealBlockChart RealBlockLimit RealBlockJacquet RealBlockDual
  RealBlockFunctional PartialJacquet JacquetLimit GramFormula PrincipalSeriesExtension
  RealPrincipalSeriesDuality JacquetNonvanishing Langlands.GeneralLinear

attribute [local instance] measurableSpaceK secondCountableTopology_unitaryCompact

local instance borelSpaceK_bn (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-! ## The approximate identity on `M_{(k+1)×a}(ℝ)` -/

section Gaussian

variable {a k : ℕ}

/-- `sqF Y = ∑_{i,j} Y_{ij}²`. -/
def sqF (Y : Fin (k + 1) → Fin a → ℝ) : ℝ := ∑ i, ∑ j, Y i j ^ 2

/-- `detF Y = det(1 + Y Yᵀ)`. -/
def detF (Y : Fin (k + 1) → Fin a → ℝ) : ℝ := (1 + Matrix.of Y * (Matrix.of Y)ᵀ).det

theorem posSemidef_gram (Y : Fin (k + 1) → Fin a → ℝ) :
    (Matrix.of Y * (Matrix.of Y)ᵀ).PosSemidef := posSemidef_self_mul_transpose _

/-- The eigenvalues of `Y Yᵀ`. -/
def eig (Y : Fin (k + 1) → Fin a → ℝ) : Fin (k + 1) → ℝ := (posSemidef_gram Y).1.eigenvalues

theorem eig_nonneg (Y : Fin (k + 1) → Fin a → ℝ) (i : Fin (k + 1)) : 0 ≤ eig Y i :=
  (posSemidef_gram Y).eigenvalues_nonneg i

theorem sum_eig (Y : Fin (k + 1) → Fin a → ℝ) : ∑ i, eig Y i = sqF Y := by
  have h := (posSemidef_gram Y).1.trace_eq_sum_eigenvalues
  simp only [RCLike.ofReal_real_eq_id, id] at h
  rw [eig, ← h, sqF, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_smul (Y : Fin (k + 1) → Fin a → ℝ) (t : ℝ) :
    Matrix.of (t • Y) * (Matrix.of (t • Y))ᵀ = (t ^ 2) • (Matrix.of Y * (Matrix.of Y)ᵀ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem detF_smul (Y : Fin (k + 1) → Fin a → ℝ) (t : ℝ) :
    detF (t • Y) = ∏ i, (1 + t ^ 2 * eig Y i) := by
  rw [detF, gram_smul, det_one_add_smul_eq_prod (posSemidef_gram Y)]
  rfl

theorem detF_eq (Y : Fin (k + 1) → Fin a → ℝ) : detF Y = ∏ i, (1 + eig Y i) := by
  have h := detF_smul Y 1
  rw [one_smul] at h
  simpa using h

theorem one_le_detF (Y : Fin (k + 1) → Fin a → ℝ) : 1 ≤ detF Y := by
  rw [detF_eq]
  have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin (k + 1) => (1 : ℝ))
    (g := fun i => 1 + eig Y i) (fun _ _ => zero_le_one)
    (fun i _ => by linarith [eig_nonneg Y i])
  simpa using h

theorem continuous_detF : Continuous (detF (a := a) (k := k)) := by
  unfold detF
  refine Continuous.matrix_det ?_
  refine continuous_const.add ?_
  exact (continuous_id.matrix_mul (continuous_id.matrix_transpose))

theorem one_add_sum_le_prod {ι : Type*} (s : Finset ι) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    nlinarith [hx j]

/-- `(1 + λ/N)^N` increases with `N`, for every eigenvalue. -/
theorem detF_pow_mono (Y : Fin (k + 1) → Fin a → ℝ) {M N : ℕ} (hM : 0 < M) (hMN : M ≤ N) :
    detF (((Real.sqrt M)⁻¹ : ℝ) • Y) ^ M ≤ detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N := by
  have hNpos : 0 < N := lt_of_lt_of_le hM hMN
  rw [detF_smul, detF_smul, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_le_prod₀ (fun i _ => pow_nonneg (by
    have := eig_nonneg Y i
    positivity) _) fun i _ => ?_
  have hsq : ∀ L : ℕ, 0 < L → ((Real.sqrt L)⁻¹) ^ 2 * eig Y i = eig Y i / L := fun L hL => by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg L), inv_mul_eq_div]
  rw [hsq M hM, hsq N hNpos]
  exact bernoulli_pow (eig_nonneg Y i) hM hMN

theorem sqF_nonneg (Y : Fin (k + 1) → Fin a → ℝ) : 0 ≤ sqF Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `(1 + sqF/M)^M ≤ detF(Y/√M)^M`. -/
theorem one_add_sqF_le (Y : Fin (k + 1) → Fin a → ℝ) {M : ℕ} (hM : 0 < M) :
    (1 + sqF Y / M) ^ M ≤ detF (((Real.sqrt M)⁻¹ : ℝ) • Y) ^ M := by
  rw [detF_smul]
  refine pow_le_pow_left₀ (by have := sqF_nonneg Y; positivity) ?_ M
  have hsq : ∀ i, ((Real.sqrt M)⁻¹) ^ 2 * eig Y i = eig Y i / M := fun i => by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg M), inv_mul_eq_div]
  simp only [hsq]
  rw [← sum_eig, Finset.sum_div]
  exact one_add_sum_le_prod Finset.univ fun i => div_nonneg (eig_nonneg Y i) (Nat.cast_nonneg M)

theorem norm_le_sqrt_sqF (Y : Fin (k + 1) → Fin a → ℝ) : ‖Y‖ ≤ Real.sqrt (sqF Y) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
  refine Real.le_sqrt_of_sq_le ?_
  rw [Real.norm_eq_abs, sq_abs]
  unfold sqF
  calc Y i j ^ 2 ≤ ∑ j', Y i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => Y i j' ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Y i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', Y i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- The exponent `M₀ = (k+1) a + 1` of the dominating function. -/
def M₀ (a k : ℕ) : ℕ := (k + 1) * a + 1

theorem finrank_rows : Module.finrank ℝ (Fin (k + 1) → Fin a → ℝ) = (k + 1) * a := by
  rw [Module.finrank_pi_fintype]
  simp

/-- The dominating function `(2M₀)^{M₀} (1 + ‖Y‖)^{-2M₀}`. -/
def bnd (a k : ℕ) (Y : Fin (k + 1) → Fin a → ℝ) : ℝ :=
  ((2 * M₀ a k : ℕ) : ℝ) ^ M₀ a k * (1 + ‖Y‖) ^ (-(2 * (M₀ a k : ℝ)))

theorem integrable_bnd : Integrable (bnd a k) := by
  refine (integrable_one_add_norm (E := Fin (k + 1) → Fin a → ℝ) (μ := volume) ?_).const_mul _
  rw [finrank_rows, M₀]
  push_cast
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]

theorem inv_detF_le_bnd (Y : Fin (k + 1) → Fin a → ℝ) {N : ℕ} (hN : M₀ a k ≤ N) :
    (detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N)⁻¹ ≤ bnd a k Y := by
  have hM0 : 0 < M₀ a k := Nat.succ_pos _
  set M := M₀ a k with hMdef
  have h1 : (1 + sqF Y / M) ^ M ≤ detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N :=
    (one_add_sqF_le Y hM0).trans (detF_pow_mono Y hM0 hN)
  have hs := sqF_nonneg Y
  -- `(1 + ‖Y‖)^{2M} ≤ (2M)^M (1 + sqF/M)^M`
  have h2 : (1 + ‖Y‖) ^ (2 * M) ≤ ((2 * M : ℕ) : ℝ) ^ M * (1 + sqF Y / M) ^ M := by
    have hb : (1 + ‖Y‖) ^ 2 ≤ ((2 * M : ℕ) : ℝ) * (1 + sqF Y / M) := by
      have hsq : ‖Y‖ ^ 2 ≤ sqF Y := by
        have := Real.sq_sqrt hs
        nlinarith [norm_nonneg Y, Real.sqrt_nonneg (sqF Y), norm_le_sqrt_sqF Y]
      have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM0
      push_cast
      rw [mul_add, mul_one, show (2 * (M : ℝ)) * (sqF Y / M) = 2 * sqF Y by field_simp]
      nlinarith [norm_nonneg Y, sq_nonneg (1 - ‖Y‖)]
    calc (1 + ‖Y‖) ^ (2 * M) = ((1 + ‖Y‖) ^ 2) ^ M := by rw [pow_mul]
      _ ≤ (((2 * M : ℕ) : ℝ) * (1 + sqF Y / M)) ^ M :=
          pow_le_pow_left₀ (by positivity) hb M
      _ = _ := mul_pow _ _ _
  have hcM : (0 : ℝ) < ((2 * M : ℕ) : ℝ) ^ M := by positivity
  have hy : 0 < (1 + ‖Y‖) ^ (2 * M) := by positivity
  have key : (1 + ‖Y‖) ^ (2 * M) ≤ ((2 * M : ℕ) : ℝ) ^ M * detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N :=
    h2.trans (mul_le_mul_of_nonneg_left h1 hcM.le)
  have hrw : (1 + ‖Y‖) ^ (-(2 * (M : ℝ))) = ((1 + ‖Y‖) ^ (2 * M))⁻¹ := by
    rw [Real.rpow_neg (by positivity), show (2 * (M : ℝ)) = ((2 * M : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  unfold bnd
  rw [← hMdef, hrw]
  have hD : 0 < detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N :=
    pow_pos (lt_of_lt_of_le zero_lt_one (one_le_detF _)) _
  calc (detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N)⁻¹ =
        (((2 * M : ℕ) : ℝ) ^ M * detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N)⁻¹ *
          ((2 * M : ℕ) : ℝ) ^ M := by
        field_simp
    _ ≤ ((1 + ‖Y‖) ^ (2 * M))⁻¹ * ((2 * M : ℕ) : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hy key) hcM.le
    _ = _ := mul_comm _ _

theorem detF_smul_pow (Y : Fin (k + 1) → Fin a → ℝ) (N : ℕ) :
    detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N = ∏ i, (1 + eig Y i / N) ^ N := by
  rw [detF_smul, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N), inv_mul_eq_div]

theorem tendsto_detF_pow (Y : Fin (k + 1) → Fin a → ℝ) :
    Tendsto (fun N : ℕ => detF (((Real.sqrt N)⁻¹ : ℝ) • Y) ^ N) atTop
      (𝓝 (Real.exp (sqF Y))) := by
  simp_rw [detF_smul_pow]
  rw [← sum_eig, Real.exp_sum]
  exact tendsto_finsetProd _ fun i _ => Real.tendsto_one_add_div_pow_exp (eig Y i)

theorem detF_pow_le_exp (Y : Fin (k + 1) → Fin a → ℝ) {M : ℕ} (hM : 0 < M) :
    detF (((Real.sqrt M)⁻¹ : ℝ) • Y) ^ M ≤ Real.exp (sqF Y) := by
  rw [detF_smul_pow, ← sum_eig, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun i _ => pow_nonneg (by
    have := eig_nonneg Y i
    positivity) _) fun i _ => ?_
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  calc (1 + eig Y i / M) ^ M ≤ Real.exp (eig Y i / M) ^ M :=
        pow_le_pow_left₀ (by have := eig_nonneg Y i; positivity)
          (by linarith [Real.add_one_le_exp (eig Y i / M)]) M
    _ = Real.exp (eig Y i) := by
        rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hMr.ne']

theorem exp_neg_le_bnd (Y : Fin (k + 1) → Fin a → ℝ) : Real.exp (-sqF Y) ≤ bnd a k Y := by
  have hM0 : 0 < M₀ a k := Nat.succ_pos _
  have hD : 0 < detF (((Real.sqrt (M₀ a k))⁻¹ : ℝ) • Y) ^ M₀ a k :=
    pow_pos (lt_of_lt_of_le zero_lt_one (one_le_detF _)) _
  rw [Real.exp_neg]
  exact (inv_anti₀ hD (detF_pow_le_exp Y hM0)).trans (inv_detF_le_bnd Y le_rfl)

theorem continuous_sqF : Continuous (sqF (a := a) (k := k)) := by
  unfold sqF
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp (continuous_apply i)).pow 2

theorem integrable_gaussianF :
    Integrable fun Y : Fin (k + 1) → Fin a → ℝ => Real.exp (-sqF Y) :=
  Integrable.mono' integrable_bnd (Real.continuous_exp.comp continuous_sqF.neg).aestronglyMeasurable
    (ae_of_all _ fun Y => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact exp_neg_le_bnd Y)

/-- `cG = ∫ exp(-∑ Y_{ij}²) dY`. -/
def cG (a k : ℕ) : ℝ := ∫ Y : Fin (k + 1) → Fin a → ℝ, Real.exp (-sqF Y)

theorem cG_pos : 0 < cG a k := by
  rw [cG, integral_pos_iff_support_of_nonneg (fun Y => (Real.exp_pos _).le) integrable_gaussianF]
  have hsupp : Function.support (fun Y : Fin (k + 1) → Fin a → ℝ => Real.exp (-sqF Y)) =
      Set.univ := Set.eq_univ_of_forall fun Y => (Real.exp_pos _).ne'
  rw [hsupp]
  exact Measure.measure_univ_pos.mpr (NeZero.ne _)

theorem sqrt_pow_rows (N : ℕ) :
    |(((Real.sqrt N)⁻¹ : ℝ) ^ Module.finrank ℝ (Fin (k + 1) → Fin a → ℝ))⁻¹| =
      Real.sqrt N ^ ((k + 1) * a) := by
  rw [finrank_rows, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]

/-- **The approximate identity.** With `N' = N + M₀`,
`√N'^{(k+1)a} ∫ det(1 + X Xᵀ)^{-N'} H(X) dX → cG · H(0)` for continuous bounded `H`. -/
theorem tendsto_concentrate {H : (Fin (k + 1) → Fin a → ℝ) → ℂ} (hH : Continuous H) {C : ℝ}
    (hC : ∀ Y, ‖H Y‖ ≤ C) :
    Tendsto (fun N : ℕ => (((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) *
        ∫ X, (((detF X ^ (N + M₀ a k))⁻¹ : ℝ) : ℂ) * H X) atTop
      (𝓝 ((cG a k : ℂ) * H 0)) := by
  set g : ℕ → (Fin (k + 1) → Fin a → ℝ) → ℂ := fun N Y =>
    (((detF (((Real.sqrt ((N + M₀ a k : ℕ) : ℝ))⁻¹ : ℝ) • Y) ^ (N + M₀ a k))⁻¹ : ℝ) : ℂ) *
      H (((Real.sqrt ((N + M₀ a k : ℕ) : ℝ))⁻¹ : ℝ) • Y) with hg
  have hsub : ∀ N : ℕ, (((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) *
      ∫ X, (((detF X ^ (N + M₀ a k))⁻¹ : ℝ) : ℂ) * H X = ∫ Y, g N Y := by
    intro N
    have h := Measure.integral_comp_smul (μ := (volume : Measure (Fin (k + 1) → Fin a → ℝ)))
      (fun X => (((detF X ^ (N + M₀ a k))⁻¹ : ℝ) : ℂ) * H X)
      ((Real.sqrt ((N + M₀ a k : ℕ) : ℝ))⁻¹)
    rw [sqrt_pow_rows, Complex.real_smul] at h
    rw [h]
  refine (tendsto_congr hsub).mpr ?_
  have hlimit : (cG a k : ℂ) * H 0 = ∫ Y : Fin (k + 1) → Fin a → ℝ,
      ((Real.exp (-sqF Y) : ℝ) : ℂ) * H 0 := by
    rw [integral_mul_const, integral_complex_ofReal]
    rfl
  rw [hlimit]
  have hM : ∀ N : ℕ, M₀ a k ≤ N + M₀ a k := fun N => Nat.le_add_left _ _
  refine tendsto_integral_of_dominated_convergence (fun Y => C * bnd a k Y) (fun N => ?_)
    (integrable_bnd.const_mul C) (fun N => ae_of_all _ fun Y => ?_) (ae_of_all _ fun Y => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    simp only [hg]
    refine Continuous.mul (Complex.continuous_ofReal.comp (Continuous.inv₀
      ((continuous_detF.comp (continuous_const_smul _)).pow _) fun Y => (pow_pos
        (lt_of_lt_of_le zero_lt_one (one_le_detF _)) _).ne')) (hH.comp (continuous_const_smul _))
  · simp only [hg]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg
      (le_trans zero_le_one (one_le_detF _)) _)), mul_comm C]
    exact mul_le_mul (inv_detF_le_bnd Y (hM N)) (hC _) (norm_nonneg _)
      (by unfold bnd; positivity)
  · simp only [hg]
    have hshift : Tendsto (fun N : ℕ => N + M₀ a k) atTop atTop := tendsto_add_atTop_nat _
    have h1 := (tendsto_detF_pow Y).comp hshift
    have h2 := h1.inv₀ (Real.exp_ne_zero _)
    rw [← Real.exp_neg] at h2
    have h3 : Tendsto (fun N : ℕ => (Real.sqrt ((N + M₀ a k : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
      have h4 : Tendsto (fun N : ℕ => Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) atTop atTop :=
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).comp hshift
      exact tendsto_inv_atTop_zero.comp h4
    have h5 : Tendsto (fun N : ℕ => ((Real.sqrt ((N + M₀ a k : ℕ) : ℝ))⁻¹ : ℝ) • Y) atTop
        (𝓝 0) := by
      simpa using h3.smul_const Y
    have h6 := (hH.tendsto 0).comp h5
    exact ((Complex.continuous_ofReal.tendsto _).comp h2).mul h6

theorem norm_concentrate_le {H : (Fin (k + 1) → Fin a → ℝ) → ℂ} {C : ℝ}
    (hC : ∀ Y, ‖H Y‖ ≤ C) (N : ℕ) :
    ‖(((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) *
        ∫ X, (((detF X ^ (N + M₀ a k))⁻¹ : ℝ) : ℂ) * H X‖ ≤ ∫ Y, C * bnd a k Y := by
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Fin (k + 1) → Fin a → ℝ)))
    (fun X => (((detF X ^ (N + M₀ a k))⁻¹ : ℝ) : ℂ) * H X)
    ((Real.sqrt ((N + M₀ a k : ℕ) : ℝ))⁻¹)
  rw [sqrt_pow_rows, Complex.real_smul] at h
  rw [← h]
  refine norm_integral_le_of_norm_le (integrable_bnd.const_mul C) (ae_of_all _ fun Y => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg
    (le_trans zero_le_one (one_le_detF _)) _)), mul_comm C]
  exact mul_le_mul (inv_detF_le_bnd Y (Nat.le_add_left _ _)) (hC _) (norm_nonneg _)
    (by unfold bnd; positivity)

end Gaussian

/-! ## Continuity of the block Jacquet functional -/

section Continuity

/-- Pointwise convergence on `O(n)` gives convergence everywhere. -/
theorem tendsto_of_mem_principalSeries {n : ℕ} {χ : ℕ → ℝˣ → ℂ}
    {f : ℕ → Langlands.GeneralLinear n ℝ → ℂ}
    {f₀ : Langlands.GeneralLinear n ℝ → ℂ} (hf : ∀ N, f N ∈ principalSeries ℝ n χ)
    (hf₀ : f₀ ∈ principalSeries ℝ n χ)
    (hlim : ∀ κ ∈ unitaryCompact ℝ n, Tendsto (fun N => f N κ) atTop (𝓝 (f₀ κ)))
    (y : Langlands.GeneralLinear n ℝ) : Tendsto (fun N => f N y) atTop (𝓝 (f₀ y)) := by
  obtain ⟨z, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact y
  have h1 : (fun N => f N ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * κ)) =
      fun N => principalSeriesCharacter ℝ n χ z * f N κ :=
    funext fun N => (hf N).2 z u κ
  rw [h1, hf₀.2 z u κ]
  exact (hlim κ hκ).const_mul _

/-- **Continuity.** `jac` is continuous for pointwise convergence on `O(n)` that is uniformly
bounded on `O(n)`. -/
theorem tendsto_jac (hT1 : RealBlockChartIntegrableStatement) :
    ∀ (ks : List ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℕ), IsSignedPower χ e →
    (∀ l : ℕ, χ l (-1) = (-1) ^ p l) →
    BlockOrdered ks e →
    ∀ {f : ℕ → Langlands.GeneralLinear (dim ks) ℝ → ℂ}
      {f₀ : Langlands.GeneralLinear (dim ks) ℝ → ℂ},
    (∀ N, f N ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks))) →
    f₀ ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)) →
    ∀ {C : ℝ}, (∀ N, ∀ κ ∈ unitaryCompact ℝ (dim ks), ‖f N κ‖ ≤ C) →
    (∀ κ ∈ unitaryCompact ℝ (dim ks), Tendsto (fun N => f N κ) atTop (𝓝 (f₀ κ))) →
    Tendsto (fun N => jac ks e p (f N)) atTop (𝓝 (jac ks e p f₀))
  | [], _, _, _, _, _, _, _, _, _, _, _, _, hlim => hlim 1 (unitaryCompact ℝ _).one_mem
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩, f, f₀, hf, hf₀, C, hC, hlim => by
    set a := dim ks
    set φ := blockVector a k e p with hφdef
    have hφc : Continuous φ := (blockVector_mem hχ hp a k).1.1.continuous
    obtain ⟨Cφ, hCφ⟩ := exists_bound_unitaryCompact hφc
    have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 1 (unitaryCompact ℝ _).one_mem)
    set D : (Fin (k + 1) → Fin a → ℝ) → ℝ := fun X => C * blockChartBound
      (fun l : Fin a => ((e ((l : ℕ) + 1)).re - (e l).re - 1) / 2) (Matrix.of X) with hD
    have hDi : Integrable D := (hT1 a (k + 1) _ (tail_h he)).const_mul C
    have hstep_bound : ∀ (N : ℕ) {κ : Langlands.GeneralLinear (a + (k + 1)) ℝ},
        κ ∈ unitaryCompact ℝ (a + (k + 1)) → ‖blockStep (f N) κ‖ ≤ ∫ X, D X :=
      fun N κ hκ => norm_blockStep_le hT1 hχ he (hf N).1 (hC N) hκ
    simp only [jac_cons]
    refine tendsto_jac hT1 ks p (isSignedPower_blockShift hχ) (blockShiftChar_neg_one k hp)
      (hks.shift _) (fun N => blockPair_mem hT1 hχ he (hf N) hφc)
      (blockPair_mem hT1 hχ he hf₀ hφc) (C := Cφ * ∫ X, D X) (fun N κ hκ => ?_)
      (fun κ hκ => ?_)
    · have := norm_integral_le_of_norm_le_const (μ := haarK (k + 1))
        (f := fun κ₂ : unitaryCompact ℝ (k + 1) =>
          φ κ₂ * blockStep (f N) (blockDiagGL κ (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)))
        (C := Cφ * ∫ X, D X) (ae_of_all _ fun κ₂ => by
          rw [norm_mul]
          exact mul_le_mul (hCφ _ κ₂.2) (hstep_bound N (blockDiagGL_mem_unitaryCompact hκ κ₂.2))
            (norm_nonneg _) hCφ0)
      simpa [blockPair] using this
    · -- the inner limit
      have hX : ∀ κ₂ : unitaryCompact ℝ (k + 1), Tendsto (fun N =>
          blockStep (f N) (blockDiagGL κ (κ₂ : Langlands.GeneralLinear (k + 1) ℝ))) atTop
          (𝓝 (blockStep f₀ (blockDiagGL κ (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)))) := by
        intro κ₂
        have hκ' := blockDiagGL_mem_unitaryCompact hκ κ₂.2
        refine tendsto_integral_of_dominated_convergence D (fun N =>
          ((hf N).1.1.continuous.comp
            (continuous_blockLowerGL.mul continuous_const)).aestronglyMeasurable)
          hDi (fun N => ae_of_all _ fun X => norm_le_block hχ he.tie (hf N).1 (hC N)
            (Matrix.of X) hκ') (ae_of_all _ fun X => ?_)
        exact tendsto_of_mem_principalSeries (fun N => (hf N).1) hf₀.1 hlim _
      refine tendsto_integral_of_dominated_convergence (fun _ => Cφ * ∫ X, D X) (fun N => ?_)
        (integrable_const _) (fun N => ae_of_all _ fun κ₂ => ?_)
        (ae_of_all _ fun κ₂ => (hX κ₂).const_mul _)
      · exact ((hφc.comp continuous_subtype_val).mul (continuous_blockStep hT1 hχ he (hf N).1
          (f₁ := fun _ => κ) continuous_const continuous_subtype_val (fun _ => hκ)
          (fun t => t.2))).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_mul (hCφ _ κ₂.2) (hstep_bound N (blockDiagGL_mem_unitaryCompact hκ κ₂.2))
          (norm_nonneg _) hCφ0

end Continuity

/-! ## Lower-right minors -/

section Minors

variable {n : ℕ}

theorem padFrom_apply_of_le {s : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (hi : s ≤ (i : ℕ))
    (hj : s ≤ (j : ℕ)) : RealBlockChart.padFrom s M i j = M i j := by
  simp [RealBlockChart.padFrom, hi, hj]

theorem padFrom_apply_of_lt_left {s : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hi : (i : ℕ) < s) :
    RealBlockChart.padFrom s M i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp [RealBlockChart.padFrom, show ¬ s ≤ (i : ℕ) by omega]

theorem padFrom_apply_of_lt_right {s : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (hj : (j : ℕ) < s) :
    RealBlockChart.padFrom s M i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simp [RealBlockChart.padFrom, show ¬ s ≤ (j : ℕ) by omega]

/-- For upper triangular `b`, `padFrom s (b y) = padFrom s b · padFrom s y`. -/
theorem padFrom_mul {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    (y : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) :
    RealBlockChart.padFrom s (b * y) =
      RealBlockChart.padFrom s b * RealBlockChart.padFrom s y := by
  have hb0 : ∀ i r : Fin n, (r : ℕ) < i → b i r = 0 := fun i r h => hb (Fin.lt_def.mpr h)
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : s ≤ (i : ℕ)
  · have hrow : ∀ r : Fin n, RealBlockChart.padFrom s b i r = b i r := by
      intro r
      by_cases hr : s ≤ (r : ℕ)
      · exact padFrom_apply_of_le b hi hr
      · rw [padFrom_apply_of_lt_right b (by omega), Matrix.one_apply_ne
          (fun h => by subst h; omega), hb0 i r (by omega)]
    simp only [hrow]
    by_cases hj : s ≤ (j : ℕ)
    · rw [padFrom_apply_of_le _ hi hj, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : s ≤ (r : ℕ)
      · rw [padFrom_apply_of_le y hr hj]
      · rw [hb0 i r (by omega), zero_mul, zero_mul]
    · rw [padFrom_apply_of_lt_right _ (by omega), Matrix.one_apply_ne
        (fun h => by subst h; omega)]
      have hcol : ∀ r : Fin n, RealBlockChart.padFrom s y r j =
          (1 : Matrix (Fin n) (Fin n) ℝ) r j := fun r => padFrom_apply_of_lt_right y (by omega)
      simp only [hcol]
      rw [← Matrix.mul_apply, Matrix.mul_one, hb0 i j (by omega)]
  · rw [padFrom_apply_of_lt_left _ (by omega)]
    have hrow : ∀ r : Fin n, RealBlockChart.padFrom s b i r =
        (1 : Matrix (Fin n) (Fin n) ℝ) i r := fun r => padFrom_apply_of_lt_left b (by omega)
    simp only [hrow]
    rw [← Matrix.mul_apply, Matrix.one_mul, padFrom_apply_of_lt_left _ (by omega)]

theorem isUpperTriangular_padFrom {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    (s : ℕ) : (RealBlockChart.padFrom s b).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  by_cases h : s ≤ (i : ℕ) ∧ s ≤ (j : ℕ)
  · rw [padFrom_apply_of_le b h.1 h.2]
    exact hb hij
  · simp only [RealBlockChart.padFrom, Matrix.of_apply, ite_eq_right h]
    exact Matrix.one_apply_ne (ne_of_lt hij).symm

theorem det_padFrom_upper {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular) (s : ℕ) :
    (RealBlockChart.padFrom s b).det = ∏ i : Fin n, if s ≤ (i : ℕ) then b i i else 1 := by
  rw [Matrix.det_of_isUpperTriangular (isUpperTriangular_padFrom hb s)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : s ≤ (i : ℕ)
  · rw [padFrom_apply_of_le b h h, ite_eq_left h]
  · rw [padFrom_apply_of_lt_left b (by omega), ite_eq_right h, Matrix.one_apply_eq]

/-- The squared lower-right minor `(det κ_{≥s,≥s})²`. -/
def minorSq (s : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (RealBlockChart.padFrom s M).det ^ 2

theorem minorSq_mul_upper {b : Matrix (Fin n) (Fin n) ℝ} (hb : b.IsUpperTriangular)
    (y : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) :
    minorSq s (b * y) = (∏ i : Fin n, if s ≤ (i : ℕ) then b i i else 1) ^ 2 * minorSq s y := by
  rw [minorSq, minorSq, padFrom_mul hb, Matrix.det_mul, det_padFrom_upper hb, mul_pow]

theorem minorSq_signDiagonal (d : Fin n → ℝ) (κ : Matrix.unitaryGroup (Fin n) ℝ) (s : ℕ) :
    minorSq s (((signDiagonal d * κ : Matrix.unitaryGroup (Fin n) ℝ)) :
      Matrix (Fin n) (Fin n) ℝ) = minorSq s (κ : Matrix (Fin n) (Fin n) ℝ) := by
  change minorSq s (Matrix.diagonal (fun i => signReal (d i)) *
    (κ : Matrix (Fin n) (Fin n) ℝ)) = _
  rw [minorSq_mul_upper (Matrix.blockTriangular_diagonal _), ← Finset.prod_pow,
    Finset.prod_eq_one, one_mul]
  intro i _
  split_ifs
  · change (Matrix.diagonal (fun i => signReal (d i)) i i) ^ 2 = 1
    rw [Matrix.diagonal_apply_eq, ← sq_abs, abs_signReal, one_pow]
  · exact one_pow _

end Minors

/-! ## Test vectors -/

section TestVector

open TranslateFinite

variable {n : ℕ}

theorem isTranslateFinite_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix.unitaryGroup (Fin n) ℝ → ℂ) (hf : ∀ i ∈ s, IsTranslateFinite id (f i)) :
    IsTranslateFinite id (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTranslateFinite_const (id : Matrix.unitaryGroup (Fin n) ℝ → _) 0
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact isTranslateFinite_add (hf i (Finset.mem_insert_self _ _))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem isTranslateFinite_prod {ι : Type*} (s : Finset ι)
    (f : ι → Matrix.unitaryGroup (Fin n) ℝ → ℂ) (hf : ∀ i ∈ s, IsTranslateFinite id (f i)) :
    IsTranslateFinite id (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTranslateFinite_const (id : Matrix.unitaryGroup (Fin n) ℝ → _) 1
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact isTranslateFinite_mul (hf i (Finset.mem_insert_self _ _))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem isTranslateFinite_det {M : Matrix.unitaryGroup (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ p q, IsTranslateFinite id (fun κ => ((M κ p q : ℝ) : ℂ))) :
    IsTranslateFinite id (fun κ => (((M κ).det : ℝ) : ℂ)) := by
  simp only [Matrix.det_apply', Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_intCast]
  exact isTranslateFinite_sum _ _ fun σ _ => isTranslateFinite_mul (isTranslateFinite_const _ _)
    (isTranslateFinite_prod _ _ fun i _ => hM _ _)

theorem isTranslateFinite_padFrom_entry (s : ℕ) (p q : Fin n) :
    IsTranslateFinite id (fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
      ((RealBlockChart.padFrom s (κ : Matrix (Fin n) (Fin n) ℝ) p q : ℝ) : ℂ)) := by
  by_cases h : s ≤ (p : ℕ) ∧ s ≤ (q : ℕ)
  · simp only [RealBlockChart.padFrom, Matrix.of_apply, ite_eq_left h]
    exact isTranslateFinite_entry (p, q)
  · simp only [RealBlockChart.padFrom, Matrix.of_apply, ite_eq_right h]
    exact isTranslateFinite_const _ _

theorem isTranslateFinite_minorSq (s : ℕ) :
    IsTranslateFinite id (fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
      ((minorSq s (κ : Matrix (Fin n) (Fin n) ℝ) : ℝ) : ℂ)) := by
  have h1 := isTranslateFinite_det (M := fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
    RealBlockChart.padFrom s (κ : Matrix (Fin n) (Fin n) ℝ))
    (isTranslateFinite_padFrom_entry s)
  simp only [minorSq, Complex.ofReal_pow]
  exact isTranslateFinite_pow h1 2

/-- `∏_{(s, N) ∈ L} (det M_{≥s,≥s})^{2N}`. -/
def bumpFactor (L : List (ℕ × ℕ)) (M : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  (L.map fun x => ((minorSq x.1 M : ℝ) : ℂ) ^ x.2).prod

theorem bumpFactor_cons (s N : ℕ) (L : List (ℕ × ℕ)) (M : Matrix (Fin n) (Fin n) ℝ) :
    bumpFactor ((s, N) :: L) M = ((minorSq s M : ℝ) : ℂ) ^ N * bumpFactor L M := rfl

theorem isTranslateFinite_bumpFactor (L : List (ℕ × ℕ)) :
    IsTranslateFinite id (fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
      bumpFactor L (κ : Matrix (Fin n) (Fin n) ℝ)) := by
  induction L with
  | nil => exact isTranslateFinite_const (id : Matrix.unitaryGroup (Fin n) ℝ → _) 1
  | cons x L ih =>
    obtain ⟨s, N⟩ := x
    simp only [bumpFactor_cons]
    exact isTranslateFinite_mul (isTranslateFinite_pow (isTranslateFinite_minorSq s) N) ih

theorem continuous_minorSq (s : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) ℝ => minorSq s M := by
  unfold minorSq
  refine (Continuous.matrix_det ?_).pow 2
  refine continuous_matrix fun p q => ?_
  by_cases h : s ≤ (p : ℕ) ∧ s ≤ (q : ℕ)
  · simp only [RealBlockChart.padFrom, Matrix.of_apply, ite_eq_left h]
    exact (continuous_apply q).comp (continuous_apply p)
  · simp only [RealBlockChart.padFrom, Matrix.of_apply, ite_eq_right h]
    exact continuous_const

theorem continuous_bumpFactor (L : List (ℕ × ℕ)) :
    Continuous fun M : Matrix (Fin n) (Fin n) ℝ => bumpFactor L M := by
  induction L with
  | nil => simpa [bumpFactor] using continuous_const
  | cons x L ih =>
    obtain ⟨s, N⟩ := x
    simp only [bumpFactor_cons]
    exact ((Complex.continuous_ofReal.comp (continuous_minorSq s)).pow N).mul ih

theorem bumpFactor_signDiagonal (L : List (ℕ × ℕ)) (d : Fin n → ℝ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    bumpFactor L (((signDiagonal d * κ : Matrix.unitaryGroup (Fin n) ℝ)) :
      Matrix (Fin n) (Fin n) ℝ) = bumpFactor L (κ : Matrix (Fin n) (Fin n) ℝ) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨s, N⟩ := x
    rw [bumpFactor_cons, bumpFactor_cons, ih, minorSq_signDiagonal]

/-- The test function `κ ↦ signMonomial(κ) · bumpFactor L κ` on `O(n)`. -/
def testFun (n : ℕ) (p a : ℕ → ℕ) (L : List (ℕ × ℕ))
    (κ : Matrix.unitaryGroup (Fin n) ℝ) : ℂ :=
  signMonomial n p a κ * bumpFactor L (κ : Matrix (Fin n) (Fin n) ℝ)

/-- The test vector: the principal-series extension of `testFun`. -/
def testVector (n : ℕ) (e : ℕ → ℂ) (p a : ℕ → ℕ) (L : List (ℕ × ℕ)) :
    Langlands.GeneralLinear n ℝ → ℂ :=
  extension (shiftedExponent n e) (testFun n p a L)

theorem continuous_testFun (p a : ℕ → ℕ) (L : List (ℕ × ℕ)) :
    Continuous (testFun n p a L) := by
  unfold testFun
  exact (continuous_signMonomial p a).mul
    ((continuous_bumpFactor L).comp continuous_subtype_val)

theorem finiteDimensional_testFun (p a : ℕ → ℕ) (L : List (ℕ × ℕ)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => testFun n p a L (x * k))) := by
  have h : IsTranslateFinite id (testFun n p a L) :=
    isTranslateFinite_mul (finiteDimensional_signMonomial p a) (isTranslateFinite_bumpFactor L)
  exact h

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

theorem testVector_mem (hχ : IsSignedPower χ e) {p : ℕ → ℕ} (hp : ∀ l, χ l (-1) = (-1) ^ p l)
    (a : ℕ → ℕ) (L : List (ℕ × ℕ)) :
    testVector n e p a L ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) := by
  refine extension_mem_kFiniteFunctions e hχ.eq (continuous_testFun p a L)
    (finiteDimensional_testFun p a L) ?_
  intro d κ
  rw [testFun, testFun, signMonomial_signDiagonal p a hp hχ.one, bumpFactor_signDiagonal]
  ring

theorem testVector_of_mem (p a : ℕ → ℕ) (L : List (ℕ × ℕ))
    {κ : Langlands.GeneralLinear n ℝ} (hκ : κ ∈ unitaryCompact ℝ n) :
    testVector n e p a L κ =
      testFun n p a L ⟨(κ : Matrix (Fin n) (Fin n) ℝ), hκ⟩ := by
  have hku : κ = Unitary.toUnits (⟨(κ : Matrix (Fin n) (Fin n) ℝ), hκ⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  calc testVector n e p a L κ = testVector n e p a L (Unitary.toUnits
        (⟨(κ : Matrix (Fin n) (Fin n) ℝ), hκ⟩ : Matrix.unitaryGroup (Fin n) ℝ)) := congrArg _ hku
    _ = _ := extension_unitary _ _ _

end TestVector

/-! ## The outer bump `Q_s(y) = (det y_{≥s,≥s})² / G_s(y)` -/

section Bump

variable {m : ℕ}

/-- `Q_s(y) = (det y_{≥s,≥s})² / G_s(y)`, left-invariant under the Borel subgroup. -/
def bumpQ (s : ℕ) (y : Langlands.GeneralLinear (m + 1) ℝ) : ℝ :=
  minorSq s (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) /
    gram s (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)

theorem bumpQ_iwasawa (z : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
    {κ : Langlands.GeneralLinear (m + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (m + 1)) (s : ℕ) :
    bumpQ s ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * κ) =
      minorSq s (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
  set y : Langlands.GeneralLinear (m + 1) ℝ :=
    (Iwasawa.diagonalUnits z : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * κ with hy
  have hval : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      (Matrix.diagonal (fun i => (z i : ℝ)) *
        ((u : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *
      (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
    rw [hy, Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
  have hP : (∏ i : Fin (m + 1), if s ≤ (i : ℕ) then (Matrix.diagonal (fun i => (z i : ℝ)) *
        ((u : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) i i
        else 1) = ∏ i : Fin (m + 1), if s ≤ (i : ℕ) then (z i : ℝ) else 1 :=
    Finset.prod_congr rfl fun i _ => by rw [diagonal_mul_apply_self]
  have hm := minorSq_mul_upper (isUpperTriangular_diagonal_mul z u)
    (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) s
  rw [hP, ← hval] at hm
  have hg : gram s (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) =
      (∏ i : Fin (m + 1), if s ≤ (i : ℕ) then (z i : ℝ) else 1) ^ 2 :=
    RealBlockChart.prod_tail_sq_eq_gram y 1 (unitaryCompact ℝ (m + 1)).one_mem z u κ hκ
      (by rw [mul_one]) s
  have hne : (∏ i : Fin (m + 1), if s ≤ (i : ℕ) then (z i : ℝ) else 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by
      split_ifs
      · exact (z i).ne_zero
      · exact one_ne_zero
  have hpos : 0 < (∏ i : Fin (m + 1), if s ≤ (i : ℕ) then (z i : ℝ) else 1) ^ 2 :=
    pow_pos (abs_pos.mpr hne) 2 |>.trans_eq (sq_abs _)
  rw [bumpQ, hm, hg]
  field_simp

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- **The outer bump.** Raising the exponent of the minor at `s` by `N` multiplies the test vector
by `Q_s^N`. -/
theorem testVector_bump (hχ : IsSignedPower χ e) {p : ℕ → ℕ} (hp : ∀ l, χ l (-1) = (-1) ^ p l)
    (a : ℕ → ℕ) (s N₁ N : ℕ) (L : List (ℕ × ℕ)) (y : Langlands.GeneralLinear (m + 1) ℝ) :
    testVector (m + 1) e p a ((s, N₁ + N) :: L) y =
      ((bumpQ s y ^ N : ℝ) : ℂ) * testVector (m + 1) e p a ((s, N₁) :: L) y := by
  obtain ⟨z, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact y
  rw [(testVector_mem hχ hp a _).1.2 z u κ, (testVector_mem hχ hp a _).1.2 z u κ,
    bumpQ_iwasawa z u hκ s, testVector_of_mem p a _ hκ, testVector_of_mem p a _ hκ]
  simp only [testFun, bumpFactor_cons]
  push_cast
  ring

end Bump

/-! ## The bump on the chart of `P_{a,k+1}` -/

section Chart

variable {a k : ℕ}

theorem gram_blockLower_rows (X : Matrix (Fin k) (Fin a) ℝ) :
    gram a (blockLower X) = (1 + X * Xᵀ).det := by
  have h := RealBlockChart.gram_blockLower_ge X (Nat.zero_le k)
  rw [Nat.add_zero] at h
  rw [h]
  set e : Fin (k - 0) ≃ Fin k := finCongr (Nat.sub_zero k) with he
  have hidx : RealBlockChart.fromIdx (Nat.zero_le k) = (e : Fin (k - 0) → Fin k) :=
    funext fun i => Fin.ext (by simp [RealBlockChart.fromIdx, he])
  rw [← Matrix.det_submatrix_equiv_self e (1 + X * Xᵀ)]
  congr 1
  ext i j
  simp only [RealBlockChart.rowsGe, hidx, Matrix.submatrix_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, id, Matrix.one_apply, e.injective.eq_iff]

theorem padFrom_blockLower_mul_blockDiag (X : Matrix (Fin k) (Fin a) ℝ)
    (A : Matrix (Fin a) (Fin a) ℝ) (D : Matrix (Fin k) (Fin k) ℝ) :
    RealBlockChart.padFrom a (blockLower X * RealBlockParabolic.blockDiag A D) =
      RealBlockParabolic.blockDiag 1 D := by
  rw [blockLower, RealBlockParabolic.blockDiag, RealBlockParabolic.blockDiag,
    reindex_mul_reindex, Matrix.fromBlocks_multiply]
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j
  · rw [padFrom_apply_of_lt_left _ (by simp)]
    simp [Matrix.one_apply, Fin.castAdd_inj]
  · rw [padFrom_apply_of_lt_left _ (by simp)]
    simp [Matrix.one_apply]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  · rw [padFrom_apply_of_lt_right _ (by simp)]
    simp [Matrix.one_apply]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  · rw [padFrom_apply_of_le _ (by simp) (by simp)]
    simp

theorem det_sq_of_mem {n : ℕ} {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n) : (κ : Matrix (Fin n) (Fin n) ℝ).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (mul_transpose_eq_one_of_mem hκ)
  rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq] at h

/-- `Q_a(n̄(X) diag(κ₁, κ₂)) = det(1 + X Xᵀ)⁻¹`. -/
theorem bumpQ_chart (X : Fin (k + 1) → Fin a → ℝ) {κ₁ : Langlands.GeneralLinear a ℝ}
    {κ₂ : Langlands.GeneralLinear (k + 1) ℝ} (hκ₁ : κ₁ ∈ unitaryCompact ℝ a)
    (hκ₂ : κ₂ ∈ unitaryCompact ℝ (k + 1)) :
    bumpQ (m := a + k) a (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL κ₁ κ₂) =
      (detF X)⁻¹ := by
  have hκ := blockDiagGL_mem_unitaryCompact hκ₁ hκ₂
  rw [bumpQ, Units.val_mul, RealBlockChart.blockLowerGL_val, blockDiagGL_val, minorSq,
    padFrom_blockLower_mul_blockDiag, RealBlockParabolic.det_blockDiag, Matrix.det_one, one_mul,
    det_sq_of_mem hκ₂, ← blockDiagGL_val,
    ParabolicChartBound.gram_mul_orthogonal _ _ (mul_transpose_eq_one_of_mem hκ),
    gram_blockLower_rows, one_div]
  rfl

end Chart

/-! ## Restriction of test vectors to the Levi factor -/

section Restrict

variable {a k : ℕ}

/-- The sign monomial as a function of a matrix. -/
def pm (n : ℕ) (p av : ℕ → ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  ∏ l : Fin n, ((M l l : ℝ) : ℂ) ^ (p l + 2 * av l)

theorem signMonomial_eq_pm {n : ℕ} (p av : ℕ → ℕ) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    signMonomial n p av κ = pm n p av (κ : Matrix (Fin n) (Fin n) ℝ) := rfl

theorem pm_blockDiag (p av : ℕ → ℕ) (A : Matrix (Fin a) (Fin a) ℝ)
    (D : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    pm (a + (k + 1)) p av (RealBlockParabolic.blockDiag A D) =
      pm a p av A * pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j)) D := by
  rw [pm, Fin.prod_univ_add]
  simp [RealBlockParabolic.blockDiag, pm, Fin.val_castAdd, Fin.val_natAdd]

theorem padFrom_blockDiag {s : ℕ} (hs : s ≤ a) (A : Matrix (Fin a) (Fin a) ℝ)
    (D : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :
    RealBlockChart.padFrom s (RealBlockParabolic.blockDiag A D) =
      RealBlockParabolic.blockDiag (RealBlockChart.padFrom s A) D := by
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => ?_) i <;>
    refine Fin.addCases (fun p' => ?_) (fun q' => ?_) j
  · simp [RealBlockChart.padFrom, RealBlockParabolic.blockDiag, Matrix.one_apply,
      Fin.castAdd_inj]
  · simp [RealBlockChart.padFrom, RealBlockParabolic.blockDiag, Matrix.one_apply]
    intro _ h
    have := congrArg Fin.val h
    simp at this
    omega
  · simp [RealBlockChart.padFrom, RealBlockParabolic.blockDiag, Matrix.one_apply]
    intro _ h
    have := congrArg Fin.val h
    simp at this
    omega
  · have h1 : s ≤ ((Fin.natAdd a q : Fin (a + (k + 1))) : ℕ) := by simp; omega
    have h2 : s ≤ ((Fin.natAdd a q' : Fin (a + (k + 1))) : ℕ) := by simp; omega
    rw [padFrom_apply_of_le _ h1 h2]
    simp [RealBlockParabolic.blockDiag]

theorem minorSq_blockDiag {s : ℕ} (hs : s ≤ a) (A : Matrix (Fin a) (Fin a) ℝ)
    {D : Langlands.GeneralLinear (k + 1) ℝ} (hD : D ∈ unitaryCompact ℝ (k + 1)) :
    minorSq s (RealBlockParabolic.blockDiag A (D : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) =
      minorSq s A := by
  rw [minorSq, minorSq, padFrom_blockDiag hs, RealBlockParabolic.det_blockDiag, mul_pow,
    det_sq_of_mem hD, mul_one]

theorem bumpFactor_blockDiag (L : List (ℕ × ℕ)) (hL : ∀ x ∈ L, x.1 ≤ a)
    (A : Matrix (Fin a) (Fin a) ℝ) {D : Langlands.GeneralLinear (k + 1) ℝ}
    (hD : D ∈ unitaryCompact ℝ (k + 1)) :
    bumpFactor L (RealBlockParabolic.blockDiag A (D : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) =
      bumpFactor L A := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    obtain ⟨s, N⟩ := x
    rw [bumpFactor_cons, bumpFactor_cons, minorSq_blockDiag (hL _ (List.mem_cons_self ..)) A hD,
      ih fun y hy => hL y (List.mem_cons_of_mem _ hy)]

theorem minorSq_self (A : Matrix (Fin a) (Fin a) ℝ) : minorSq a A = 1 := by
  have h : RealBlockChart.padFrom a A = 1 := by
    ext i j
    rw [padFrom_apply_of_lt_left _ i.isLt]
  rw [minorSq, h, Matrix.det_one, one_pow]

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- **Restriction.** On `diag(κ₁, κ₂)` with orthogonal `κ₁, κ₂`, the test vector of
`GL_{a+k+1}(ℝ)` is the test vector of `GL_a(ℝ)` at `κ₁` times the block sign monomial at `κ₂`. -/
theorem testVector_blockDiag (e' : ℕ → ℂ) (p av : ℕ → ℕ) (L : List (ℕ × ℕ))
    (hL : ∀ x ∈ L, x.1 ≤ a) {κ₁ : Langlands.GeneralLinear a ℝ}
    {κ₂ : Langlands.GeneralLinear (k + 1) ℝ} (hκ₁ : κ₁ ∈ unitaryCompact ℝ a)
    (hκ₂ : κ₂ ∈ unitaryCompact ℝ (k + 1)) :
    testVector (a + (k + 1)) e p av L (blockDiagGL κ₁ κ₂) =
      testVector a e' p av L κ₁ *
        pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j))
          (κ₂ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := by
  rw [testVector_of_mem p av L (blockDiagGL_mem_unitaryCompact hκ₁ hκ₂),
    testVector_of_mem p av L hκ₁]
  simp only [testFun, signMonomial_eq_pm]
  rw [blockDiagGL_val, pm_blockDiag, bumpFactor_blockDiag L hL _ hκ₂]
  ring

end Restrict

/-! ## Nonvanishing -/

theorem integrable_of_continuous_unitary_real {n : ℕ} {f : unitaryCompact ℝ n → ℝ}
    (hf : Continuous f) : Integrable f (haarK n) :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

section Main

variable {a k : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

theorem blockChartBound_le_one {ε : Fin a → ℝ} (hε : ∀ l, ε l ≤ 0)
    (X : Matrix (Fin (k + 1)) (Fin a) ℝ) : blockChartBound ε X ≤ 1 := by
  unfold blockChartBound
  have h1 : ∏ l, colGram X l ^ ε l ≤ 1 :=
    Finset.prod_le_one₀ (fun l _ => Real.rpow_nonneg
      (le_trans zero_le_one (one_le_colGram X l)) _) fun l _ =>
        Real.rpow_le_one_of_one_le_of_nonpos (one_le_colGram X l) (hε l)
  have hrow0 : ∀ j : Fin (k + 1),
      0 ≤ (if (j : ℕ) = 0 then (1 : ℝ) else rowGram X j ^ (-(1 / 2 : ℝ))) := fun j => by
    split_ifs
    · exact zero_le_one
    · exact Real.rpow_nonneg (le_trans zero_le_one (one_le_rowGram X j)) _
  have h2 : ∏ j : Fin (k + 1),
      (if (j : ℕ) = 0 then (1 : ℝ) else rowGram X j ^ (-(1 / 2 : ℝ))) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => hrow0 j) fun j _ => by
      split_ifs
      · exact le_rfl
      · exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_rowGram X j) (by norm_num)
  have h0 : 0 ≤ ∏ j : Fin (k + 1),
      (if (j : ℕ) = 0 then (1 : ℝ) else rowGram X j ^ (-(1 / 2 : ℝ))) :=
    Finset.prod_nonneg fun j _ => hrow0 j
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 h0 zero_le_one
    _ = 1 := one_mul 1

theorem norm_chart_le (hχ : IsSignedPower χ e) (he : IsBlockDominant e a k)
    {h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ} (hh : h ∈ principalSeries ℝ (a + (k + 1)) χ)
    {C : ℝ} (hC : ∀ κ ∈ unitaryCompact ℝ (a + (k + 1)), ‖h κ‖ ≤ C) (hC0 : 0 ≤ C)
    (X : Fin (k + 1) → Fin a → ℝ) {κ : Langlands.GeneralLinear (a + (k + 1)) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (a + (k + 1))) :
    ‖h (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * κ)‖ ≤ C :=
  (norm_le_block hχ he.tie hh hC (Matrix.of X) hκ).trans (mul_le_of_le_one_right hC0
    (blockChartBound_le_one (fun l => by linarith [he.ord l l.isLt]) _))

theorem blockStep_smul (c : ℂ) (f : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)
    (g : Langlands.GeneralLinear (a + (k + 1)) ℝ) : blockStep (c • f) g = c * blockStep f g := by
  simp only [blockStep, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem testVector_bump_block (hχ : IsSignedPower χ e) {p : ℕ → ℕ}
    (hp : ∀ l, χ l (-1) = (-1) ^ p l)
    (av : ℕ → ℕ) (s N : ℕ) (L : List (ℕ × ℕ)) (y : Langlands.GeneralLinear (a + (k + 1)) ℝ) :
    testVector (a + (k + 1)) e p av ((s, N) :: L) y =
      ((bumpQ (m := a + k) s y ^ N : ℝ) : ℂ) * testVector (a + (k + 1)) e p av ((s, 0) :: L) y := by
  have h := testVector_bump (m := a + k) hχ hp av s 0 N L y
  rw [zero_add] at h
  exact h

/-- The pairing of the dual block sign vector with the block sign monomial is positive. -/
theorem exists_integral_blockVector_pm (e : ℕ → ℂ) (p av : ℕ → ℕ) (a k : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∫ κ₂ : unitaryCompact ℝ (k + 1), blockVector a k e p κ₂ *
      pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j))
        ((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
      ∂haarK (k + 1) = (r : ℂ) := by
  set c : Fin (k + 1) → ℕ := fun j => p (a + j) + av (a + j) with hc
  set g : unitaryCompact ℝ (k + 1) → ℝ := fun κ₂ => ∏ j : Fin (k + 1),
    ((((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) j j) ^ 2) ^ c j with hg
  have hpt : ∀ κ₂ : unitaryCompact ℝ (k + 1), blockVector a k e p κ₂ *
      pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j))
        ((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) =
      ((g κ₂ : ℝ) : ℂ) := by
    intro κ₂
    rw [blockVector, signVector_of_mem _ _ κ₂.2, signMonomial_eq_pm, pm, pm,
      ← Finset.prod_mul_distrib, hg, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hc, Pi.zero_apply, mul_zero, add_zero]
    push_cast
    ring
  have hgc : Continuous g := by
    simp only [hg]
    refine continuous_finsetProd (f := fun (j : Fin (k + 1)) (κ₂ : unitaryCompact ℝ (k + 1)) =>
      ((((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) j j) ^ 2) ^ c j) _ fun j _ => ?_
    have hval : Continuous fun κ₂ : unitaryCompact ℝ (k + 1) =>
        ((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) :=
      (Units.continuous_val : Continuous (Units.val : Langlands.GeneralLinear (k + 1) ℝ →
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)).comp continuous_subtype_val
    exact ((hval.matrix_elem j j).pow 2).pow (c j)
  have hg0 : 0 ≤ g := fun κ₂ => Finset.prod_nonneg fun j _ => pow_nonneg (sq_nonneg _) _
  have hg1 : g 1 = 1 := by
    simp only [hg]
    refine Finset.prod_eq_one fun j _ => ?_
    simp [Matrix.one_apply_eq]
  refine ⟨∫ κ₂, g κ₂ ∂haarK (k + 1), ?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg hg0 (integrable_of_continuous_unitary_real hgc)]
    exact (hgc.isOpen_support).measure_pos _
      ⟨1, by rw [Function.mem_support, hg1]; exact one_ne_zero⟩
  · rw [integral_congr_ae (ae_of_all _ hpt), integral_complex_ofReal]

/-- **Nonvanishing of the block Jacquet functional.** For every block decomposition with
`BlockOrdered ks e`, some test vector of the principal series of `χ` has nonzero `jac`. -/
theorem exists_jac_testVector_ne_zero (hT1 : RealBlockChartIntegrableStatement) :
    ∀ (ks : List ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℕ), IsSignedPower χ e →
    (∀ l : ℕ, χ l (-1) = (-1) ^ p l) →
    BlockOrdered ks e →
    ∃ (av : ℕ → ℕ) (L : List (ℕ × ℕ)), (∀ x ∈ L, x.1 ≤ dim ks) ∧
      jac ks e p (testVector (dim ks) e p av L) ≠ 0
  | [], χ, e, p, _, _, _ => by
      refine ⟨0, [], by simp, ?_⟩
      change testVector 0 e p 0 [] 1 ≠ 0
      rw [testVector_of_mem p 0 [] (unitaryCompact ℝ 0).one_mem]
      simp [testFun, signMonomial, bumpFactor]
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩ => by
      obtain ⟨av, L, hL, hne⟩ := exists_jac_testVector_ne_zero hT1 ks p
        (isSignedPower_blockShift (k := k) hχ) (blockShiftChar_neg_one k hp)
        (hks.shift (((k : ℂ) + 1) / 2))
      set a := dim ks with ha
      have hχ' := isSignedPower_blockShift (k := k) hχ
      have hp' := blockShiftChar_neg_one k hp
      have hφm := blockVector_mem hχ hp a k
      have hφc : Continuous (blockVector a k e p) := hφm.1.1.continuous
      obtain ⟨Cφ, hCφ⟩ := exists_bound_unitaryCompact hφc
      have hCφ0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 1 (unitaryCompact ℝ _).one_mem)
      obtain ⟨r, hr, hI⟩ := exists_integral_blockVector_pm e p av a k
      have hL0 : ∀ x ∈ (a, 0) :: L, x.1 ≤ a := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact hL x hx
      have hTV0 := testVector_mem (n := a + (k + 1)) hχ hp av ((a, 0) :: L)
      obtain ⟨C₀, hC₀⟩ := exists_bound_unitaryCompact hTV0.1.1.continuous
      have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 1 (unitaryCompact ℝ _).one_mem)
      have hTVN : ∀ N : ℕ, testVector (a + (k + 1)) e p av ((a, N + M₀ a k) :: L) ∈
          kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ) (unitaryCompact ℝ (a + (k + 1))) :=
        fun N => testVector_mem hχ hp av _
      -- the partial Jacquet integral of the bumped test vector
      have hstep : ∀ (N : ℕ) {κ₁ : Langlands.GeneralLinear a ℝ}
          {κ₂ : Langlands.GeneralLinear (k + 1) ℝ}, κ₁ ∈ unitaryCompact ℝ a →
          κ₂ ∈ unitaryCompact ℝ (k + 1) →
          blockStep (testVector (a + (k + 1)) e p av ((a, N + M₀ a k) :: L))
            (blockDiagGL κ₁ κ₂) = ∫ X, (((detF X ^ (N + M₀ a k))⁻¹ : ℝ) : ℂ) *
              testVector (a + (k + 1)) e p av ((a, 0) :: L)
                (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL κ₁ κ₂) := by
        intro N κ₁ κ₂ hκ₁ hκ₂
        unfold blockStep
        refine integral_congr_ae (ae_of_all _ fun X => ?_)
        simp only
        rw [testVector_bump_block hχ hp av a (N + M₀ a k) L, bumpQ_chart X hκ₁ hκ₂, inv_pow]
      have hHb : ∀ {κ₁ : Langlands.GeneralLinear a ℝ} {κ₂ : Langlands.GeneralLinear (k + 1) ℝ},
          κ₁ ∈ unitaryCompact ℝ a → κ₂ ∈ unitaryCompact ℝ (k + 1) →
          ∀ X : Fin (k + 1) → Fin a → ℝ, ‖testVector (a + (k + 1)) e p av ((a, 0) :: L)
            (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL κ₁ κ₂)‖ ≤ C₀ :=
        fun hκ₁ hκ₂ X => norm_chart_le hχ he hTV0.1 hC₀ hC₀0 X
          (blockDiagGL_mem_unitaryCompact hκ₁ hκ₂)
      -- concentration at `X = 0`
      have hconc : ∀ {κ₁ : Langlands.GeneralLinear a ℝ} {κ₂ : Langlands.GeneralLinear (k + 1) ℝ},
          κ₁ ∈ unitaryCompact ℝ a → κ₂ ∈ unitaryCompact ℝ (k + 1) →
          Tendsto (fun N : ℕ => (((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) *
            blockStep (testVector (a + (k + 1)) e p av ((a, N + M₀ a k) :: L))
              (blockDiagGL κ₁ κ₂)) atTop
            (𝓝 ((cG a k : ℂ) * (testVector a (fun l => e l - ((k : ℂ) + 1) / 2) p av L κ₁ *
              pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j))
                (κ₂ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)))) := by
        intro κ₁ κ₂ hκ₁ hκ₂
        have hH : Continuous fun X : Fin (k + 1) → Fin a → ℝ =>
            testVector (a + (k + 1)) e p av ((a, 0) :: L)
              (blockLowerGL (a := a) (k := k + 1) (Matrix.of X) * blockDiagGL κ₁ κ₂) :=
          hTV0.1.1.continuous.comp (continuous_blockLowerGL.mul continuous_const)
        have h := tendsto_concentrate hH (hHb hκ₁ hκ₂)
        have h0 : testVector (a + (k + 1)) e p av ((a, 0) :: L)
            (blockLowerGL (a := a) (k := k + 1) (Matrix.of (0 : Fin (k + 1) → Fin a → ℝ)) *
              blockDiagGL κ₁ κ₂) =
            testVector a (fun l => e l - ((k : ℂ) + 1) / 2) p av L κ₁ *
              pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j))
                (κ₂ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) := by
          rw [show Matrix.of (0 : Fin (k + 1) → Fin a → ℝ) = 0 from rfl, blockLowerGL_zero,
            one_mul, testVector_blockDiag (fun l => e l - ((k : ℂ) + 1) / 2) p av _ hL0 hκ₁ hκ₂]
          congr 1
          rw [testVector_of_mem p av _ hκ₁, testVector_of_mem p av L hκ₁]
          simp only [testFun, bumpFactor_cons, pow_zero, one_mul]
        rw [h0] at h
        refine (tendsto_congr fun N => ?_).mpr h
        rw [hstep N hκ₁ hκ₂]
      have hconc_le : ∀ (N : ℕ) {κ₁ : Langlands.GeneralLinear a ℝ}
          {κ₂ : Langlands.GeneralLinear (k + 1) ℝ}, κ₁ ∈ unitaryCompact ℝ a →
          κ₂ ∈ unitaryCompact ℝ (k + 1) →
          ‖(((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) *
            blockStep (testVector (a + (k + 1)) e p av ((a, N + M₀ a k) :: L))
              (blockDiagGL κ₁ κ₂)‖ ≤ ∫ X, C₀ * bnd a k X := by
        intro N κ₁ κ₂ hκ₁ hκ₂
        rw [hstep N hκ₁ hκ₂]
        exact norm_concentrate_le (hHb hκ₁ hκ₂) N
      -- the functions on `GL_a(ℝ)`
      have hf : ∀ N : ℕ, blockPair (blockVector a k e p)
          ((((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) •
            testVector (a + (k + 1)) e p av ((a, N + M₀ a k) :: L)) ∈
          kFiniteFunctions (principalSeries ℝ a (blockShiftChar k χ)) (unitaryCompact ℝ a) :=
        fun N => blockPair_mem hT1 hχ he (Submodule.smul_mem _ _ (hTVN N)) hφc
      have hf₀ := Submodule.smul_mem _ ((cG a k : ℂ) * (r : ℂ))
        (testVector_mem (n := a) hχ' hp' av L)
      have hlim := tendsto_jac hT1 ks p hχ' hp' (hks.shift (((k : ℂ) + 1) / 2)) hf hf₀
        (C := Cφ * ∫ X, C₀ * bnd a k X)
        (fun N κ₁ hκ₁ => by
          have := norm_integral_le_of_norm_le_const (μ := haarK (k + 1))
            (C := Cφ * ∫ X, C₀ * bnd a k X)
            (f := fun κ₂ : unitaryCompact ℝ (k + 1) => blockVector a k e p κ₂ *
              blockStep ((((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) •
                testVector (a + (k + 1)) e p av ((a, N + M₀ a k) :: L))
                  (blockDiagGL κ₁ (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)))
            (ae_of_all _ fun κ₂ => by
              rw [norm_mul, blockStep_smul]
              exact mul_le_mul (hCφ _ κ₂.2) (hconc_le N hκ₁ κ₂.2) (norm_nonneg _) hCφ0)
          simpa [blockPair] using this)
        (fun κ₁ hκ₁ => by
          simp only [blockPair, blockStep_smul]
          have hval : (((cG a k : ℂ) * (r : ℂ)) •
              testVector a (fun l => e l - ((k : ℂ) + 1) / 2) p av L) κ₁ =
              ∫ κ₂ : unitaryCompact ℝ (k + 1), blockVector a k e p κ₂ *
                ((cG a k : ℂ) * (testVector a (fun l => e l - ((k : ℂ) + 1) / 2) p av L κ₁ *
                  pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j))
                    ((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) :
                      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))) ∂haarK (k + 1) := by
            have heq : ∀ κ₂ : unitaryCompact ℝ (k + 1), blockVector a k e p κ₂ *
                ((cG a k : ℂ) * (testVector a (fun l => e l - ((k : ℂ) + 1) / 2) p av L κ₁ *
                  pm (k + 1) (fun j => p (a + j)) (fun j => av (a + j))
                    ((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) :
                      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))) =
                ((cG a k : ℂ) * testVector a (fun l => e l - ((k : ℂ) + 1) / 2) p av L κ₁) *
                  (blockVector a k e p κ₂ * pm (k + 1) (fun j => p (a + j))
                    (fun j => av (a + j)) ((κ₂ : Langlands.GeneralLinear (k + 1) ℝ) :
                      Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) := fun κ₂ => by ring
            rw [integral_congr_ae (ae_of_all _ heq), integral_const_mul, hI, Pi.smul_apply,
              smul_eq_mul]
            ring
          rw [hval]
          refine tendsto_integral_of_dominated_convergence (fun _ => Cφ * ∫ X, C₀ * bnd a k X)
            (fun N => ?_) (integrable_const _) (fun N => ae_of_all _ fun κ₂ => ?_)
            (ae_of_all _ fun κ₂ => (hconc hκ₁ κ₂.2).const_mul _)
          · refine ((hφc.comp continuous_subtype_val).mul (continuous_const.mul
              (continuous_blockStep hT1 hχ he (hTVN N).1 (f₁ := fun _ => κ₁) continuous_const
                continuous_subtype_val (fun _ => hκ₁) (fun t => t.2)))).aestronglyMeasurable
          · rw [norm_mul]
            exact mul_le_mul (hCφ _ κ₂.2) (hconc_le N hκ₁ κ₂.2) (norm_nonneg _) hCφ0)
      have hne' : jac ks (fun l => e l - ((k : ℂ) + 1) / 2) p
          (((cG a k : ℂ) * (r : ℂ)) • testVector a (fun l => e l - ((k : ℂ) + 1) / 2) p av L) ≠
            0 := by
        rw [jac_smul]
        refine mul_ne_zero (mul_ne_zero ?_ ?_) hne
        · exact_mod_cast (cG_pos (a := a) (k := k)).ne'
        · exact_mod_cast hr.ne'
      obtain ⟨N, hN⟩ := (hlim.eventually (isOpen_ne.mem_nhds hne')).exists
      refine ⟨av, (a, N + M₀ a k) :: L, ?_, fun h0 => hN ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · change a ≤ a + (k + 1)
          omega
        · exact le_trans (hL x hx) (show a ≤ a + (k + 1) by omega)
      · have h1 : jac (k :: ks) e p
            ((((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) •
            testVector (dim (k :: ks)) e p av ((a, N + M₀ a k) :: L)) =
            (((Real.sqrt ((N + M₀ a k : ℕ) : ℝ)) ^ ((k + 1) * a) : ℝ) : ℂ) *
              jac (k :: ks) e p (testVector (dim (k :: ks)) e p av ((a, N + M₀ a k) :: L)) :=
          jac_smul _ _ _ _ _
        rw [h0, mul_zero, jac_cons] at h1
        exact h1

end Main

end RealBlockNonvanishing

/-- **The block Jacquet functional does not vanish** (assuming
`RealBlockChartIntegrableStatement`). Let `ks` be a block decomposition of
`n = RealBlockFunctional.dim ks` and `χ` characters of `ℝˣ` with
`χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and `χ_l(−1) = (−1)^{p_l}`, such that
`RealBlockFunctional.BlockOrdered ks e`. Then some `O(n)`-finite function `f` of the smooth
principal series of `χ` has `RealBlockFunctional.jac ks e p f ≠ 0`. -/
def RealBlockNonvanishingStatement : Prop :=
  RealBlockChartIntegrableStatement →
  ∀ (ks : List ℕ) (χ : ℕ → ℝˣ → ℂ) (e : ℕ → ℂ) (p : ℕ → ℕ),
    (∀ (l : ℕ) (x : ℝˣ), χ l x =
      χ l (GramFormula.signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ l : ℕ, χ l (-1) = (-1) ^ p l) →
    RealBlockFunctional.BlockOrdered ks e →
    ∃ f ∈ kFiniteFunctions (principalSeries ℝ (RealBlockFunctional.dim ks) χ)
      (unitaryCompact ℝ (RealBlockFunctional.dim ks)), RealBlockFunctional.jac ks e p f ≠ 0

theorem realBlockNonvanishing : RealBlockNonvanishingStatement := by
  intro hT1 ks χ e p heq hone hp hks
  have hχ : PartialJacquet.IsSignedPower χ e :=
    ⟨heq, hone, fun l => by rw [hp, norm_pow, norm_neg, norm_one, one_pow]⟩
  obtain ⟨av, L, -, hne⟩ := RealBlockNonvanishing.exists_jac_testVector_ne_zero hT1 ks p hχ hp hks
  exact ⟨_, RealBlockNonvanishing.testVector_mem hχ hp av L, hne⟩

end Langlands.Archimedean

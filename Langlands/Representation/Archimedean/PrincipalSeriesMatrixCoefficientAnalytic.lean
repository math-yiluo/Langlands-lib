import Langlands.Representation.Archimedean.PrincipalSeriesGramFormula
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Analyticity of `O(n)`-finite matrix coefficients of real principal series
-/

noncomputable section

open Matrix MeasureTheory Metric Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace MatrixCoefficientAnalytic

open GramFormula

variable {n : ℕ}

/-! ## Complex differentiability of Gram expressions along curves -/

section Differentiable

theorem differentiableAt_finset_prod {ι : Type*} (s : Finset ι) {g : ι → ℂ → ℂ} {z : ℂ}
    (h : ∀ i ∈ s, DifferentiableAt ℂ (g i) z) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ s, g i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem differentiableAt_det {Z : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (h : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z) :
    DifferentiableAt ℂ (fun w => (Z w).det) z := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact DifferentiableAt.fun_sum fun σ _ =>
    (differentiableAt_const _).mul (differentiableAt_finset_prod _ fun i _ => h (σ i) i)

theorem differentiableAt_mul_transpose {Z : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (h : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z) (p q : Fin n) :
    DifferentiableAt ℂ (fun w => (Z w * (Z w)ᵀ) p q) z := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact DifferentiableAt.fun_sum fun r _ => (h p r).mul (h q r)

theorem differentiableAt_paddedGram {Z : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (h : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z) (i : ℕ) (p q : Fin n) :
    DifferentiableAt ℂ (fun w => paddedGram i (Z w) p q) z := by
  simp only [paddedGram, Matrix.of_apply]
  split_ifs
  · exact differentiableAt_mul_transpose h p q
  · exact differentiableAt_const _

theorem differentiableAt_gram {Z : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (h : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z) (i : ℕ) :
    DifferentiableAt ℂ (fun w => gram i (Z w)) z :=
  differentiableAt_det (differentiableAt_paddedGram h i)

theorem differentiableAt_gramColumn {Z : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (h : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z) (i j : Fin n) :
    DifferentiableAt ℂ (fun w => gramColumn i j (Z w)) z := by
  refine differentiableAt_det fun p q => ?_
  simp only [Matrix.updateCol_apply, gramColumnVector]
  split_ifs
  · exact h p j
  · exact differentiableAt_const _
  · exact differentiableAt_paddedGram h i p q

theorem differentiableAt_mvPolynomial_eval {σ : Type*} (P : MvPolynomial σ ℂ)
    {v : σ → ℂ → ℂ} {z : ℂ} (h : ∀ s, DifferentiableAt ℂ (v s) z) :
    DifferentiableAt ℂ (fun w => MvPolynomial.eval (fun s => v s w) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p s hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (h s)

theorem mem_slitPlane_of_re_pos {w : ℂ} (hw : 0 < w.re) : w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl hw)

/-- A Gram expression is complex differentiable along a curve with differentiable entries at
a point where all Gram determinants have positive real part. -/
theorem differentiableAt_gramExpression (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    {Z : ℂ → Matrix (Fin n) (Fin n) ℂ} {z : ℂ}
    (h : ∀ p q, DifferentiableAt ℂ (fun w => Z w p q) z)
    (hpos : ∀ l : ℕ, l ≤ n → 0 < (gram l (Z z)).re) :
    DifferentiableAt ℂ (fun w => gramExpression s P (Z w)) z := by
  have hG : ∀ (l : ℕ) (c : ℂ), l ≤ n → DifferentiableAt ℂ (fun w => gram l (Z w) ^ c) z :=
    fun l c hl => (differentiableAt_gram h l).cpow_const (mem_slitPlane_of_re_pos (hpos l hl))
  unfold gramExpression
  refine (differentiableAt_finset_prod _ fun (l : Fin n) _ =>
    (hG (l : ℕ) _ l.isLt.le).mul (hG ((l : ℕ) + 1) _ l.isLt)).mul ?_
  exact differentiableAt_mvPolynomial_eval P fun ij =>
    ((differentiableAt_gramColumn h ij.1 ij.2).mul (hG ij.1 _ ij.1.isLt.le)).mul
      (hG (ij.1 + 1) _ ij.1.isLt)

end Differentiable

/-! ## Continuity of Gram expressions -/

section Continuous

variable {X : Type*} [TopologicalSpace X]

theorem continuous_paddedGram {Z : X → Matrix (Fin n) (Fin n) ℂ} (h : Continuous Z) (i : ℕ) :
    Continuous fun y => paddedGram i (Z y) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [paddedGram, Matrix.of_apply]
  split_ifs
  · simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact continuous_finsetSum _ fun r _ =>
      ((continuous_apply r).comp ((continuous_apply p).comp h)).mul
        ((continuous_apply r).comp ((continuous_apply q).comp h))
  · exact continuous_const

theorem continuous_gram {Z : X → Matrix (Fin n) (Fin n) ℂ} (h : Continuous Z) (i : ℕ) :
    Continuous fun y => gram i (Z y) :=
  (continuous_paddedGram h i).matrix_det

theorem continuous_gramColumn {Z : X → Matrix (Fin n) (Fin n) ℂ} (h : Continuous Z)
    (i j : Fin n) : Continuous fun y => gramColumn i j (Z y) := by
  refine Continuous.matrix_det (continuous_pi fun p => continuous_pi fun q => ?_)
  simp only [Matrix.updateCol_apply, gramColumnVector]
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply p).comp h)
  · exact continuous_const
  · exact (continuous_apply q).comp ((continuous_apply p).comp (continuous_paddedGram h i))

/-- A Gram expression is continuous along a continuous family of matrices at the points where
all Gram determinants have positive real part. -/
theorem continuousAt_gramExpression (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    {Z : X → Matrix (Fin n) (Fin n) ℂ} (h : Continuous Z) {x : X}
    (hpos : ∀ l : ℕ, l ≤ n → 0 < (gram l (Z x)).re) :
    ContinuousAt (fun y => gramExpression s P (Z y)) x := by
  have hG : ∀ (l : ℕ) (c : ℂ), l ≤ n → ContinuousAt (fun y => gram l (Z y) ^ c) x :=
    fun l c hl => ((continuous_gram h l).continuousAt).cpow continuousAt_const
      (mem_slitPlane_of_re_pos (hpos l hl))
  unfold gramExpression
  refine (tendsto_finsetProd _ fun (l : Fin n) _ =>
    (hG (l : ℕ) _ l.isLt.le).mul (hG ((l : ℕ) + 1) _ l.isLt)).mul ?_
  have hv : ContinuousAt (fun y => fun ij : Fin n × Fin n =>
      gramColumn ij.1 ij.2 (Z y) * gram (ij.1 : ℕ) (Z y) ^ (-(1 / 2 : ℂ)) *
        gram ((ij.1 : ℕ) + 1) (Z y) ^ (-(1 / 2 : ℂ))) x :=
    continuousAt_pi.mpr fun ij =>
      (((continuous_gramColumn h ij.1 ij.2).continuousAt).mul (hG ij.1 _ ij.1.isLt.le)).mul
        (hG (ij.1 + 1) _ ij.1.isLt)
  exact (MvPolynomial.continuous_eval P).continuousAt.comp hv

end Continuous

/-! ## Holomorphic parameter integrals over compact spaces -/

section Integral

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem integrable_of_continuous_of_compact {f : X → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => hC x trivial)

/-- **Holomorphic parameter integrals.** If `F` is jointly continuous on `closedBall z₀ R × X` and
holomorphic in `z` on `ball z₀ R` for every `x`, then `z ↦ ∫ F z x dμ` has complex derivative
`∫ ∂_z F z₀ x dμ` at `z₀`. -/
theorem hasDerivAt_integral_of_holomorphic {F : ℂ → X → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (Function.uncurry F) (closedBall z₀ R ×ˢ Set.univ))
    (hd : ∀ x, DifferentiableOn ℂ (fun z => F z x) (ball z₀ R)) :
    HasDerivAt (fun z => ∫ x, F z x ∂μ) (∫ x, deriv (fun z => F z x) z₀ ∂μ) z₀ := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall z₀ R).prod isCompact_univ).exists_bound_of_continuousOn hc
  have hcont : ∀ z ∈ closedBall z₀ R, Continuous (F z) := fun z hz =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ x⟩
  have hρ : 0 < R / 2 := half_pos hR
  have hderiv : ∀ x, ∀ z ∈ ball z₀ R,
      HasDerivAt (fun w => F w x) (deriv (fun w => F w x) z) z :=
    fun x z hz => ((hd x).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hmeas' : AEStronglyMeasurable (fun x => deriv (fun z => F z x) z₀) μ := by
    let δ : ℕ → ℝ := fun m => R / 2 * (1 / ((m : ℝ) + 1))
    have hδpos : ∀ m, 0 < δ m := fun m => mul_pos hρ (by positivity)
    have hδle : ∀ m, δ m ≤ R / 2 := fun m => by
      have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      calc δ m ≤ R / 2 * 1 := mul_le_mul_of_nonneg_left h1 hρ.le
        _ = R / 2 := mul_one _
    have hδ0 : Tendsto δ atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (R / 2)
      rw [mul_zero] at h
      exact h
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun m x => ((δ m : ℂ))⁻¹ • (F (z₀ + δ m) x - F z₀ x)) (fun m => ?_)
      (ae_of_all _ fun x => ?_)
    · have h1 : z₀ + (δ m : ℂ) ∈ closedBall z₀ R := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hδpos m)]
        linarith [hδle m]
      have hsub : Continuous fun x => F (z₀ + δ m) x - F z₀ x :=
        (hcont _ h1).sub (hcont z₀ (mem_closedBall_self hR.le))
      have hc' : Continuous (fun x => ((δ m : ℂ))⁻¹ * (F (z₀ + δ m) x - F z₀ x)) :=
        continuous_const.mul hsub
      exact hc'.aestronglyMeasurable
    · have hT := hasDerivAt_iff_tendsto_slope_zero.mp (hderiv x z₀ (mem_ball_self hR))
      refine hT.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => ?_⟩)
      · have h := (Complex.continuous_ofReal.tendsto 0).comp hδ0
        rw [Complex.ofReal_zero] at h
        exact h
      · simpa using (hδpos m).ne'
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball z₀ (R / 2))
    (F' := fun z x => deriv (fun w => F w x) z) (bound := fun _ => C / (R / 2))
    (ball_mem_nhds z₀ hρ) ?_ ?_ hmeas' ?_ (integrable_const _) ?_).2
  · filter_upwards [ball_mem_nhds z₀ hR] with z hz
    exact (hcont z (ball_subset_closedBall hz)).aestronglyMeasurable
  · exact integrable_of_continuous_of_compact μ (hcont z₀ (mem_closedBall_self hR.le))
  · refine ae_of_all _ fun x z hz => ?_
    have hsub : closedBall z (R / 2) ⊆ ball z₀ R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball] at hz ⊢
      linarith [dist_triangle w z z₀]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
      ((hd x).diffContOnCl_ball hsub) fun w hw => ?_
    exact hC (w, x) ⟨ball_subset_closedBall (hsub (sphere_subset_closedBall hw)),
      Set.mem_univ x⟩
  · exact ae_of_all _ fun x z hz => hderiv x z (ball_subset_ball (by linarith) hz)

theorem differentiableOn_integral_of_holomorphic {F : ℂ → X → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (Function.uncurry F) (closedBall z₀ R ×ˢ Set.univ))
    (hd : ∀ x, DifferentiableOn ℂ (fun z => F z x) (ball z₀ R)) :
    DifferentiableOn ℂ (fun z => ∫ x, F z x ∂μ) (ball z₀ (R / 2)) := by
  intro z hz
  have hz' : dist z z₀ < R / 2 := hz
  refine (hasDerivAt_integral_of_holomorphic μ (z₀ := z) (R := R / 2) (half_pos hR)
    (hc.mono ?_) fun x => (hd x).mono ?_).differentiableAt.differentiableWithinAt
  · exact Set.prod_mono (closedBall_subset_closedBall' (by linarith)) le_rfl
  · exact ball_subset_ball' (by linarith)

theorem analyticAt_integral_of_holomorphic {F : ℂ → X → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ContinuousOn (Function.uncurry F) (closedBall z₀ R ×ˢ Set.univ))
    (hd : ∀ x, DifferentiableOn ℂ (fun z => F z x) (ball z₀ R)) :
    AnalyticAt ℂ (fun z => ∫ x, F z x ∂μ) z₀ :=
  (differentiableOn_integral_of_holomorphic μ hR hc hd).analyticAt
    (ball_mem_nhds z₀ (half_pos hR))

end Integral

/-! ## Real analyticity -/

theorem analyticAt_comp_ofReal {f : ℂ → ℂ} {t : ℝ} (hf : AnalyticAt ℂ f (t : ℂ)) :
    AnalyticAt ℝ (fun s : ℝ => f (s : ℂ)) t :=
  (hf.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)

/-- A real analytic function on `ℝ` all of whose derivatives vanish at `0` is zero. -/
theorem eq_zero_of_iteratedDeriv_eq_zero {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f Set.univ)
    (h : ∀ j, iteratedDeriv j f 0 = 0) : f = 0 := by
  have h1 : analyticOrderAt f 0 = ⊤ :=
    ENat.eq_top_iff_forall_ge.mpr fun m =>
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf 0 trivial)).mpr fun i _ => h i
  have h2 : f =ᶠ[𝓝 0] 0 := analyticOrderAt_eq_top.mp h1
  funext t
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    h2 (Set.mem_univ t)

/-! ## Diagonal one-parameter subgroups -/

/-- The diagonal one-parameter subgroup `t ↦ diag(e^(t h_0), …, e^(t h_(n-1)))` of `GL_n(ℝ)`. -/
def expDiagonal (h : Fin n → ℝ) (t : ℝ) : Langlands.GeneralLinear n ℝ :=
  Iwasawa.diagonalUnits fun j => Units.mk0 (Real.exp (t * h j)) (Real.exp_pos _).ne'

theorem expDiagonal_val (h : Fin n → ℝ) (t : ℝ) :
    ((expDiagonal h t : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.diagonal fun j => Real.exp (t * h j) :=
  rfl

theorem expDiagonal_add (h : Fin n → ℝ) (s t : ℝ) :
    expDiagonal h (s + t) = expDiagonal h s * expDiagonal h t := by
  apply Units.ext
  rw [Units.val_mul, expDiagonal_val, expDiagonal_val, expDiagonal_val,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  rw [add_mul, Real.exp_add]

theorem expDiagonal_zero (h : Fin n → ℝ) : expDiagonal h 0 = 1 := by
  apply Units.ext
  rw [expDiagonal_val]
  simp

/-- The derivative at `0` of `s ↦ f(p · exp(s H))`, `H = diag(h)`, is `(R(H) f)(p)`. -/
theorem hasDerivAt_mul_expDiagonal {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (p : Langlands.GeneralLinear n ℝ)
    (h : Fin n → ℝ) :
    HasDerivAt (fun s => f (p * expDiagonal h s))
      (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) f p) 0 := by
  have hγ : ∀ i j, HasDerivAt
      (fun s => ((expDiagonal h s : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) i j) (Matrix.diagonal h i j) 0 := by
    intro i j
    simp only [expDiagonal_val, Matrix.diagonal_apply]
    split_ifs with hij
    · have := ((hasDerivAt_id (0 : ℝ)).mul_const (h i)).exp
      simpa using this
    · exact hasDerivAt_const _ _
  have hc : HasDerivAt (fun s => (p : Matrix (Fin n) (Fin n) ℝ) *
      ((expDiagonal h s : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))
      ((p : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal h) 0 :=
    (hasDerivAt_matrix_of_entries hγ).const_mul (p : Matrix (Fin n) (Fin n) ℝ)
  have hc0 : (p : Matrix (Fin n) (Fin n) ℝ) *
      ((expDiagonal h 0 : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
        (p : Matrix (Fin n) (Fin n) ℝ) := by
    rw [expDiagonal_zero, Units.val_one, mul_one]
  have hd : HasFDerivAt (unitsExtension f)
      (fderiv ℝ (unitsExtension f) (p : Matrix (Fin n) (Fin n) ℝ))
      ((p : Matrix (Fin n) (Fin n) ℝ) *
        ((expDiagonal h 0 : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [hc0]
    exact (differentiableAt_unitsExtension hf (Units.isUnit p)).hasFDerivAt
  have hfun : (fun s => f (p * expDiagonal h s)) = unitsExtension f ∘ fun s =>
      (p : Matrix (Fin n) (Fin n) ℝ) *
        ((expDiagonal h s : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
    funext s
    rw [Function.comp_apply, ← unitsExtension_val f (p * expDiagonal h s), Units.val_mul]
  rw [hfun, rightDerivative_eq_fderiv hf]
  exact hd.comp_hasDerivAt (0 : ℝ) hc

/-- The derivative at `t` of `s ↦ f(x · exp(s H))` is `(R(H) f)(x · exp(t H))`. -/
theorem hasDerivAt_mul_expDiagonal_at {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (x : Langlands.GeneralLinear n ℝ)
    (h : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => f (x * expDiagonal h s))
      (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) f (x * expDiagonal h t)) t := by
  have h0 : HasDerivAt (fun s => f (x * expDiagonal h t * expDiagonal h s))
      (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) f (x * expDiagonal h t))
      (t - t) := by
    rw [sub_self]
    exact hasDerivAt_mul_expDiagonal hf _ h
  convert HasDerivAt.comp_sub_const t t h0 using 1
  funext s
  rw [mul_assoc, ← expDiagonal_add, add_sub_cancel]

/-! ## Complexified curves -/

/-- The complexified curve `z ↦ κ g diag(e^(z h_0), …, e^(z h_(n-1)))`, for `κ ∈ O(n)`. -/
def complexCurve (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) (z : ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  complexify ((κ : Matrix (Fin n) (Fin n) ℝ) * (g : Matrix (Fin n) (Fin n) ℝ)) *
    Matrix.diagonal fun j => Complex.exp (z * h j)

theorem complexCurve_apply (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) (z : ℂ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) (p q : Fin n) :
    complexCurve g h z κ p q =
      ((((κ : Matrix (Fin n) (Fin n) ℝ) * (g : Matrix (Fin n) (Fin n) ℝ)) p q : ℝ) : ℂ) *
        Complex.exp (z * h q) := by
  rw [complexCurve, Matrix.mul_diagonal]
  rfl

theorem complexCurve_ofReal (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) (t : ℝ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    complexCurve g h t κ = complexify ((Unitary.toUnits κ * g * expDiagonal h t :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  ext p q
  rw [complexCurve_apply, Units.val_mul, Units.val_mul, expDiagonal_val, complexify,
    Matrix.map_apply, Matrix.mul_diagonal, Complex.ofRealHom_eq_coe]
  push_cast
  rfl

theorem continuous_complexCurve (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) :
    Continuous fun x : ℂ × Matrix.unitaryGroup (Fin n) ℝ => complexCurve g h x.1 x.2 := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [complexCurve_apply]
  have hm : Continuous fun κ : Matrix.unitaryGroup (Fin n) ℝ =>
      (κ : Matrix (Fin n) (Fin n) ℝ) * (g : Matrix (Fin n) (Fin n) ℝ) :=
    continuous_subtype_val.matrix_mul continuous_const
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp
      (((continuous_apply q).comp ((continuous_apply p).comp hm)).comp continuous_snd)
  · exact Complex.continuous_exp.comp (continuous_fst.mul continuous_const)

theorem differentiableAt_complexCurve (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ)
    (κ : Matrix.unitaryGroup (Fin n) ℝ) (z : ℂ) (p q : Fin n) :
    DifferentiableAt ℂ (fun w => complexCurve g h w κ p q) z := by
  simp only [complexCurve_apply]
  exact (differentiableAt_const _).mul ((differentiableAt_id.mul_const _).cexp)

theorem gram_complexCurve_ofReal_re_pos (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ)
    (t : ℝ) (κ : Matrix.unitaryGroup (Fin n) ℝ) (l : ℕ) :
    0 < (gram l (complexCurve g h t κ)).re := by
  rw [complexCurve_ofReal, complexify, gram_map]
  simpa using gram_pos (Unitary.toUnits κ * g * expDiagonal h t) l

/-- The pairs `(z, κ)` at which all Gram determinants of the complexified curve have positive
real part. -/
def goodSet (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) :
    Set (ℂ × Matrix.unitaryGroup (Fin n) ℝ) :=
  ⋂ l : Fin (n + 1), {x | 0 < (gram (l : ℕ) (complexCurve g h x.1 x.2)).re}

theorem isOpen_goodSet (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) :
    IsOpen (goodSet g h) :=
  isOpen_iInter_of_finite fun l => isOpen_lt continuous_const
    (Complex.continuous_re.comp (continuous_gram (continuous_complexCurve g h) l))

theorem mem_goodSet_iff {g : Langlands.GeneralLinear n ℝ} {h : Fin n → ℝ}
    {x : ℂ × Matrix.unitaryGroup (Fin n) ℝ} :
    x ∈ goodSet g h ↔ ∀ l : ℕ, l ≤ n → 0 < (gram l (complexCurve g h x.1 x.2)).re := by
  simp only [goodSet, Set.mem_iInter, Set.mem_ofPred_eq]
  exact ⟨fun H l hl => H ⟨l, Nat.lt_succ_of_le hl⟩, fun H l => H l (Nat.lt_succ_iff.mp l.isLt)⟩

/-- The integrand `gramExpression s P (κ g diag(e^(z h))) · φ(κ)` of the complexified matrix
coefficient. -/
def gramIntegrand (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ)
    (z : ℂ) (κ : Matrix.unitaryGroup (Fin n) ℝ) : ℂ :=
  gramExpression s P (complexCurve g h z κ) * φ κ

theorem differentiableAt_gramIntegrand (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ)
    {z : ℂ} {κ : Matrix.unitaryGroup (Fin n) ℝ} (hx : (z, κ) ∈ goodSet g h) :
    DifferentiableAt ℂ (fun w => gramIntegrand s P g h φ w κ) z := by
  have hpos := (mem_goodSet_iff (x := (z, κ))).mp hx
  have hD := differentiableAt_gramExpression s P (Z := fun w => complexCurve g h w κ)
    (fun p q => differentiableAt_complexCurve g h κ z p q) hpos
  exact hD.mul_const (φ κ)

theorem continuousAt_gramIntegrand (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ}
    (hφ : Continuous φ) {x : ℂ × Matrix.unitaryGroup (Fin n) ℝ} (hx : x ∈ goodSet g h) :
    ContinuousAt (Function.uncurry (gramIntegrand s P g h φ)) x := by
  have hpos := (mem_goodSet_iff (x := x)).mp hx
  have hC := continuousAt_gramExpression s P (continuous_complexCurve g h) hpos
  exact hC.mul (hφ.comp continuous_snd).continuousAt

/-- Near every real point the complexified curve stays in `goodSet` for all `κ`. -/
theorem exists_closedBall_subset_goodSet (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ)
    (t₀ : ℝ) : ∃ R > 0, ∀ z ∈ closedBall (t₀ : ℂ) R, ∀ κ, (z, κ) ∈ goodSet g h := by
  have hgood : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ, ((t₀ : ℂ), κ) ∈ goodSet g h := fun κ =>
    mem_goodSet_iff.mpr fun l _ => gram_complexCurve_ofReal_re_pos g h t₀ κ l
  have hev : ∀ᶠ z in 𝓝 (t₀ : ℂ), ∀ κ ∈ (Set.univ : Set (Matrix.unitaryGroup (Fin n) ℝ)),
      (z, κ) ∈ goodSet g h :=
    isCompact_univ.eventually_forall_of_forall_eventually fun κ _ =>
      (isOpen_goodSet g h).mem_nhds (hgood κ)
  obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨ε / 2, half_pos hε, fun z hz κ =>
    hεU (lt_of_le_of_lt (mem_closedBall.mp hz) (half_lt_self hε)) κ (Set.mem_univ κ)⟩

/-! ## Matrix coefficients along diagonal one-parameter subgroups -/

section MatrixCoefficient

variable (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)) [IsFiniteMeasure μ]

/-- The `O(n)`-integral matrix coefficient `g ↦ ∫ f(κ g) φ(κ) dμ(κ)`. -/
def matrixCoefficient (f : Langlands.GeneralLinear n ℝ → ℂ)
    (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ∫ κ, f (Unitary.toUnits κ * g) * φ κ ∂μ

/-- **Analyticity.** For an `O(n)`-finite function `f` of a principal series and a continuous
`φ` on `O(n)`, the matrix coefficient `t ↦ ∫ f(κ g exp(tH)) φ(κ) dμ(κ)` along a diagonal
one-parameter subgroup is real analytic, with derivative the matrix coefficient of `R(H) f`. -/
theorem analyticAt_matrixCoefficient {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))
    {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ} (hφ : Continuous φ)
    (g : Langlands.GeneralLinear n ℝ) (h : Fin n → ℝ) (t₀ : ℝ) :
    AnalyticAt ℝ (fun t => matrixCoefficient μ f φ (g * expDiagonal h t)) t₀ ∧
      HasDerivAt (fun t => matrixCoefficient μ f φ (g * expDiagonal h t))
        (matrixCoefficient μ (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) f) φ
          (g * expDiagonal h t₀)) t₀ := by
  obtain ⟨P, hP⟩ := exists_gramExpression_eq e hχ hf
  have hsmooth := (Submodule.mem_inf.mp hf).1.1
  let F : ℂ → Matrix.unitaryGroup (Fin n) ℝ → ℂ := gramIntegrand (shiftedExponent n e) P g h φ
  have hFreal : ∀ (t : ℝ) κ, F t κ = f (Unitary.toUnits κ * (g * expDiagonal h t)) * φ κ := by
    intro t κ
    simp only [F, gramIntegrand]
    rw [complexCurve_ofReal, ← hP, mul_assoc]
  obtain ⟨R, hR, hball⟩ := exists_closedBall_subset_goodSet g h t₀
  have hc : ContinuousOn (Function.uncurry F) (closedBall (t₀ : ℂ) R ×ˢ Set.univ) := by
    rintro ⟨z, κ⟩ ⟨hz, -⟩
    exact (continuousAt_gramIntegrand (shiftedExponent n e) P g h hφ
      (hball z hz κ)).continuousWithinAt
  have hd : ∀ κ, DifferentiableOn ℂ (fun z => F z κ) (ball (t₀ : ℂ) R) := fun κ z hz =>
    (differentiableAt_gramIntegrand (shiftedExponent n e) P g h φ
      (hball z (ball_subset_closedBall hz) κ)).differentiableWithinAt
  have hΨ : (fun t : ℝ => ∫ κ, F t κ ∂μ) =
      fun t => matrixCoefficient μ f φ (g * expDiagonal h t) := by
    funext t
    simp only [matrixCoefficient]
    exact integral_congr_ae (ae_of_all _ fun κ => hFreal t κ)
  constructor
  · rw [← hΨ]
    exact analyticAt_comp_ofReal (analyticAt_integral_of_holomorphic μ hR hc hd)
  · have hD := (hasDerivAt_integral_of_holomorphic μ hR hc hd).comp_ofReal
    rw [hΨ] at hD
    convert hD using 1
    simp only [matrixCoefficient]
    refine integral_congr_ae (ae_of_all _ fun κ => ?_)
    have h1 : HasDerivAt (fun z => F z κ) (deriv (fun z => F z κ) (t₀ : ℂ)) (t₀ : ℂ) :=
      ((hd κ).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))).hasDerivAt
    have h3 : HasDerivAt (fun y : ℝ => F y κ)
        (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) f
          (Unitary.toUnits κ * (g * expDiagonal h t₀)) * φ κ) t₀ := by
      have := (hasDerivAt_mul_expDiagonal_at hsmooth (Unitary.toUnits κ * g) h t₀).mul_const
        (φ κ)
      simp only [mul_assoc] at this
      convert this using 1
      funext y
      rw [hFreal]
    exact (h1.comp_ofReal.unique h3).symm

/-- **One-parameter vanishing.** Let `W` be a space of `O(n)`-finite functions of a principal
series, stable under `R(H)` for `H = diag(h)`. If `∫ w(κ g) φ(κ) dμ(κ) = 0` for all `w ∈ W`,
then `∫ w(κ g exp(tH)) φ(κ) dμ(κ) = 0` for all `w ∈ W` and all real `t`. -/
theorem matrixCoefficient_mul_expDiagonal_eq_zero {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)
    {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) (h : Fin n → ℝ)
    (hWD : ∀ w ∈ W, rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) w ∈ W)
    {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ} (hφ : Continuous φ)
    (g : Langlands.GeneralLinear n ℝ) (h0 : ∀ w ∈ W, matrixCoefficient μ w φ g = 0) :
    ∀ w ∈ W, ∀ t : ℝ, matrixCoefficient μ w φ (g * expDiagonal h t) = 0 := by
  have hderiv : ∀ w ∈ W, deriv (fun t => matrixCoefficient μ w φ (g * expDiagonal h t)) =
      fun t => matrixCoefficient μ (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) w) φ
        (g * expDiagonal h t) := fun w hw => funext fun t =>
    (analyticAt_matrixCoefficient μ e hχ (hW hw) hφ g h t).2.deriv
  have hiter : ∀ j : ℕ, ∀ w ∈ W,
      iteratedDeriv j (fun t => matrixCoefficient μ w φ (g * expDiagonal h t)) 0 = 0 := by
    intro j
    induction j with
    | zero =>
      intro w hw
      rw [iteratedDeriv_zero, expDiagonal_zero, mul_one]
      exact h0 w hw
    | succ j ih =>
      intro w hw
      rw [iteratedDeriv_succ', hderiv w hw]
      exact ih _ (hWD w hw)
  intro w hw t
  have := eq_zero_of_iteratedDeriv_eq_zero
    (fun t _ => (analyticAt_matrixCoefficient μ e hχ (hW hw) hφ g h t).1) (hiter · w hw)
  exact congrFun this t

end MatrixCoefficient

/-! ## The `KAK` decomposition -/

theorem diagonal_mem_unitaryGroup_iff_aux {d : Fin n → ℝ} :
    star (Matrix.diagonal d) = Matrix.diagonal d := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  simp

/-- **`KAK` decomposition.** Every `g ∈ GL_n(ℝ)` is `k₁ · exp(H) · k₂` with `k₁, k₂ ∈ O(n)` and
`H` diagonal. -/
theorem exists_kak (g : Langlands.GeneralLinear n ℝ) :
    ∃ k₁ ∈ unitaryCompact ℝ n, ∃ k₂ ∈ unitaryCompact ℝ n, ∃ h : Fin n → ℝ,
      g = k₁ * expDiagonal h 1 * k₂ := by
  classical
  set G : Matrix (Fin n) (Fin n) ℝ := (g : Matrix (Fin n) (Fin n) ℝ) with hGdef
  have hinj : Function.Injective G.mulVec := by
    intro x y hxy
    have := congrArg (fun v => ((g⁻¹ : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) *ᵥ v) hxy
    simpa [G, Matrix.mulVec_mulVec] using this
  have hA : (Gᴴ * G).PosDef := Matrix.PosDef.conjTranspose_mul_self G hinj
  set U : Matrix.unitaryGroup (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary with hUdef
  set lam : Fin n → ℝ := hA.isHermitian.eigenvalues with hlamdef
  have hlam : ∀ i, 0 < lam i := hA.eigenvalues_pos
  have hD : star (U : Matrix (Fin n) (Fin n) ℝ) * (Gᴴ * G) * (U : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.diagonal lam := by
    have := hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [this]
    congr 1
  set sq : Fin n → ℝ := fun i => Real.sqrt (lam i) with hsqdef
  have hsq : ∀ i, 0 < sq i := fun i => Real.sqrt_pos.mpr (hlam i)
  let sU : Fin n → ℝˣ := fun i => Units.mk0 (sq i) (hsq i).ne'
  let k₁ : Langlands.GeneralLinear n ℝ :=
    g * Unitary.toUnits U * Iwasawa.diagonalUnits sU⁻¹
  have hk₁val : (k₁ : Matrix (Fin n) (Fin n) ℝ) =
      G * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal fun i => (sq i)⁻¹ := by
    simp only [k₁, Units.val_mul]
    rfl
  have hUU : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  have hk₁ : k₁ ∈ unitaryCompact ℝ n := by
    change (k₁ : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.unitaryGroup (Fin n) ℝ
    rw [Matrix.mem_unitaryGroup_iff', hk₁val, star_mul, star_mul, diagonal_mem_unitaryGroup_iff_aux]
    have hG : star G = Gᴴ := rfl
    calc Matrix.diagonal (fun i => (sq i)⁻¹) * (star (U : Matrix (Fin n) (Fin n) ℝ) * star G) *
          (G * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal fun i => (sq i)⁻¹)
        = Matrix.diagonal (fun i => (sq i)⁻¹) *
            (star (U : Matrix (Fin n) (Fin n) ℝ) * (Gᴴ * G) * (U : Matrix (Fin n) (Fin n) ℝ)) *
              Matrix.diagonal (fun i => (sq i)⁻¹) := by
          rw [hG]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext i
          have h2 : sq i * sq i = lam i := Real.mul_self_sqrt (hlam i).le
          rw [← h2]
          field_simp [(hsq i).ne']
  have hk₂ : Unitary.toUnits (star U) ∈ unitaryCompact ℝ n := (star U).2
  refine ⟨k₁, hk₁, Unitary.toUnits (star U), hk₂, fun i => Real.log (sq i), ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hk₁val, expDiagonal_val]
  have hexp : (Matrix.diagonal fun j => Real.exp (1 * Real.log (sq j))) = Matrix.diagonal sq := by
    congr 1
    funext j
    rw [one_mul, Real.exp_log (hsq j)]
  rw [hexp]
  change G = G * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (fun i => (sq i)⁻¹) *
    Matrix.diagonal sq * star (U : Matrix (Fin n) (Fin n) ℝ)
  rw [Matrix.mul_assoc G, Matrix.mul_assoc G, Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ),
    Matrix.diagonal_mul_diagonal]
  have hone : (Matrix.diagonal fun i => (sq i)⁻¹ * sq i) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hsq i).ne'
  rw [hone, Matrix.mul_one, Matrix.mul_assoc, hUU, Matrix.mul_one]

/-! ## Orthogonality invariance -/

section Invariance

variable (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem matrixCoefficient_mul_unitary (f : Langlands.GeneralLinear n ℝ → ℂ)
    (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ) (g k : Langlands.GeneralLinear n ℝ) :
    matrixCoefficient μ f φ (g * k) =
      matrixCoefficient μ (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f) φ g := by
  simp only [matrixCoefficient]
  refine integral_congr_ae (ae_of_all _ fun κ => ?_)
  change f (Unitary.toUnits κ * (g * k)) * φ κ = f (Unitary.toUnits κ * g * k) * φ κ
  rw [mul_assoc]

/-- **Orthogonality invariance.** Let `W` be a subspace of the `O(n)`-finite functions of a
principal series that is stable under right translation by `O(n)` and under the right
derivatives `R(X)`, `X ∈ 𝔤𝔩_n(ℝ)`, and let `φ` be continuous on `O(n)`. If
`∫ w(κ) φ(κ) dμ(κ) = 0` for all `w ∈ W`, then `∫ w(κ g) φ(κ) dμ(κ) = 0` for all `w ∈ W` and all
`g ∈ GL_n(ℝ)`. -/
theorem matrixCoefficient_eq_zero {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)
    {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))
    (hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W)
    (hWD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W, rightDerivative (matrixModel ℝ n) X w ∈ W)
    {φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ} (hφ : Continuous φ)
    (h1 : ∀ w ∈ W, matrixCoefficient μ w φ 1 = 0) :
    ∀ w ∈ W, ∀ g, matrixCoefficient μ w φ g = 0 := by
  intro w hw g
  obtain ⟨k₁, hk₁, k₂, hk₂, h, rfl⟩ := exists_kak g
  rw [matrixCoefficient_mul_unitary]
  have hk1 : ∀ w ∈ W, matrixCoefficient μ w φ k₁ = 0 := fun w hw => by
    have := matrixCoefficient_mul_unitary μ w φ 1 k₁
    rw [one_mul] at this
    rw [this]
    exact h1 _ (hWK k₁ hk₁ w hw)
  exact matrixCoefficient_mul_expDiagonal_eq_zero μ e hχ hW h
    (fun w hw => hWD _ w hw) hφ k₁ hk1 _ (hWK k₂ hk₂ w hw) 1

end Invariance

end MatrixCoefficientAnalytic

open MatrixCoefficientAnalytic

/-- **Statement (orthogonality invariance for real principal series).** Let `ds` be a list of
real blocks, `W` a subspace of the `O(n)`-finite functions of the smooth principal series of the
position characters of `ds`, stable under right translation by `O(n)` and under the right
derivatives `R(X)`, `X ∈ 𝔤𝔩_n(ℝ)`. Let `μ` be a finite measure on `O(n)` and `φ` a continuous
function on `O(n)`. If `∫ w(κ) φ(κ) dμ(κ) = 0` for every `w ∈ W`, then
`∫ w(κ g) φ(κ) dμ(κ) = 0` for every `w ∈ W` and every `g ∈ GL_n(ℝ)`. -/
def PrincipalSeriesOrthogonalityInvarianceStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)),
    W ≤ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n) →
    (∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W) →
    (∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W, rightDerivative (matrixModel ℝ n) X w ∈ W) →
    ∀ (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)), IsFiniteMeasure μ →
    ∀ (φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ), Continuous φ →
      (∀ w ∈ W, ∫ κ, w (Unitary.toUnits κ) * φ κ ∂μ = 0) →
        ∀ w ∈ W, ∀ g : Langlands.GeneralLinear n ℝ,
          ∫ κ, w (Unitary.toUnits κ * g) * φ κ ∂μ = 0

theorem principalSeriesOrthogonalityInvariance :
    PrincipalSeriesOrthogonalityInvarianceStatement := by
  intro n ds W hW hWK hWD μ _ φ hφ h1 w hw g
  have h1' : ∀ w ∈ W, MatrixCoefficientAnalytic.matrixCoefficient μ w φ 1 = 0 := fun w hw => by
    simp only [MatrixCoefficientAnalytic.matrixCoefficient, mul_one]
    exact h1 w hw
  exact matrixCoefficient_eq_zero μ (GramFormula.realPositionExponent ds)
    (GramFormula.realPositionCharacter_eq_signUnit_mul ds) hW hWK hWD hφ h1' w hw g

end Langlands.Archimedean

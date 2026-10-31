import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Powerset
import Langlands.Analysis.CoordinateScalarDifferentialOperator

/-!
# Uniform factorial bounds for the derivatives of real-analytic functions

A real-analytic function `f` satisfies, near every point `x₀`, the Cauchy-type estimates
`‖D^j f y‖ ≤ C * A ^ j * j!` for all orders `j` and all `y` in one ball around `x₀`, with
constants `C`, `A` independent of `y` and `j`.

* `HasFactorialDerivativeBoundsOn f s C A` is the predicate `∀ y ∈ s, ∀ j, ‖D^j f y‖ ≤ C A^j j!`
  (operator norm of the iterated Fréchet derivative over `ℝ`).
* `exists_ball_hasFactorialDerivativeBoundsOn_of_analyticAt`: `AnalyticAt ℝ f x₀` gives a ball
  around `x₀` and constants with these bounds; `exists_ball_le_hasFactorialDerivativeBoundsOn_of_analyticAt`
  also makes the radius at most a prescribed `R₀` and records analyticity on the ball.
* `CoordinateScalarOperator.AnalyticCoefficientsOn.exists_ball_hasFactorialDerivativeBoundsOn`:
  the finitely many coefficients of a coordinate scalar differential operator that are analytic
  near `x₀ ∈ S` admit one common ball and common constants.

The proof expands `f` around `y` by `p.changeOrigin (y - x₀)` and bounds its coefficients by a
geometric series, using `‖D^j f y‖ ≤ j! ‖q j‖` for a power series `q` of `f` at `y`.
-/

noncomputable section
set_option autoImplicit false

open scoped ENNReal NNReal Topology
open Equiv

namespace Langlands.Analysis

universe uE uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Factorial bounds for all real iterated Fréchet derivatives of `f` on `s` with constants
`C` and `A`: `‖D^j f y‖ ≤ C * A ^ j * j!` for every `y ∈ s` and every order `j`. -/
def HasFactorialDerivativeBoundsOn (f : E → F) (s : Set E) (C A : ℝ) : Prop :=
  ∀ y ∈ s, ∀ j : ℕ, ‖iteratedFDeriv ℝ j f y‖ ≤ C * A ^ j * (j.factorial : ℝ)

namespace HasFactorialDerivativeBoundsOn

variable {f : E → F} {s t : Set E} {C C' A A' : ℝ}

theorem norm_iteratedFDeriv_le (h : HasFactorialDerivativeBoundsOn f s C A) {y : E}
    (hy : y ∈ s) (j : ℕ) : ‖iteratedFDeriv ℝ j f y‖ ≤ C * A ^ j * (j.factorial : ℝ) :=
  h y hy j

/-- The bound applied to vectors, for instance to words of basis vectors. -/
theorem norm_iteratedFDeriv_apply_le (h : HasFactorialDerivativeBoundsOn f s C A) {y : E}
    (hy : y ∈ s) {j : ℕ} (v : Fin j → E) :
    ‖iteratedFDeriv ℝ j f y v‖ ≤ C * A ^ j * (j.factorial : ℝ) * ∏ i, ‖v i‖ :=
  ((iteratedFDeriv ℝ j f y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (h y hy j) (by positivity))

theorem mono (h : HasFactorialDerivativeBoundsOn f s C A) (hts : t ⊆ s) :
    HasFactorialDerivativeBoundsOn f t C A :=
  fun y hy => h y (hts hy)

theorem mono_const (h : HasFactorialDerivativeBoundsOn f s C A) (hA : 0 ≤ A) (hC : C ≤ C')
    (hA' : A ≤ A') : HasFactorialDerivativeBoundsOn f s C' A' := by
  intro y hy j
  have hC0 : 0 ≤ C := by
    have h0 := h y hy 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at h0
    exact (norm_nonneg _).trans h0
  have hC'0 : 0 ≤ C' := hC0.trans hC
  refine (h y hy j).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact mul_le_mul hC (pow_le_pow_left₀ hA hA' j) (pow_nonneg hA j) hC'0

end HasFactorialDerivativeBoundsOn

/-- At the center of a power series expansion `p`, the `j`-th iterated derivative has operator
norm at most `j! ‖p j‖`. -/
theorem norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries ℝ E F} {x : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) (j : ℕ) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ (j.factorial : ℝ) * ‖p j‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [hf.iteratedFDeriv_eq_sum_of_completeSpace v]
  calc ‖∑ σ : Perm (Fin j), p j (fun i => v (σ i))‖
      ≤ ∑ σ : Perm (Fin j), ‖p j (fun i => v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Perm (Fin j), ‖p j‖ * ∏ i, ‖v i‖ := by
        gcongr with σ
        calc ‖p j (fun i => v (σ i))‖ ≤ ‖p j‖ * ∏ i, ‖v (σ i)‖ := (p j).le_opNorm _
          _ = ‖p j‖ * ∏ i, ‖v i‖ := by rw [Equiv.prod_comp σ (fun i => ‖v i‖)]
    _ = (j.factorial : ℝ) * ‖p j‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]

/-- The terms of `p.changeOriginSeries k` evaluated on a constant vector. -/
theorem norm_changeOriginSeries_apply_le (p : FormalMultilinearSeries ℝ E F) (k l : ℕ)
    (x : E) :
    ‖p.changeOriginSeries k l (fun _ => x)‖ ≤ 2 ^ (k + l) * ‖p (k + l)‖ * ‖x‖ ^ l := by
  have h1 : ‖p.changeOriginSeries k l‖ ≤ 2 ^ (k + l) * ‖p (k + l)‖ := by
    calc ‖p.changeOriginSeries k l‖
        ≤ ∑ s : { s : Finset (Fin (k + l)) // s.card = l },
            ‖p.changeOriginSeriesTerm k l s s.2‖ := by
          unfold FormalMultilinearSeries.changeOriginSeries
          exact norm_sum_le Finset.univ
            (fun s : { s : Finset (Fin (k + l)) // s.card = l } =>
              p.changeOriginSeriesTerm k l s.1 s.2)
      _ = ((k + l).choose l : ℝ) * ‖p (k + l)‖ := by
          simp only [FormalMultilinearSeries.norm_changeOriginSeriesTerm, Finset.sum_const,
            Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 2 ^ (k + l) * ‖p (k + l)‖ := by
          gcongr
          exact_mod_cast Nat.choose_le_two_pow (k + l) l
  calc ‖p.changeOriginSeries k l (fun _ => x)‖
      ≤ ‖p.changeOriginSeries k l‖ * ∏ _i : Fin l, ‖x‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖p.changeOriginSeries k l‖ * ‖x‖ ^ l := by rw [Fin.prod_const]
    _ ≤ 2 ^ (k + l) * ‖p (k + l)‖ * ‖x‖ ^ l := by gcongr

/-- If `‖p n‖ r ^ n ≤ C` for all `n` and `‖x‖ ≤ r / 4`, then the coefficients of the series
re-expanded at `x` satisfy `‖(p.changeOrigin x) k‖ ≤ 2 C (2 / r) ^ k`. -/
theorem norm_changeOrigin_le (p : FormalMultilinearSeries ℝ E F) {r : ℝ≥0} {C : ℝ}
    (hr : 0 < r) (hC : ∀ n, ‖p n‖ * (r : ℝ) ^ n ≤ C) {x : E} (hx : ‖x‖ ≤ r / 4) (k : ℕ) :
    ‖p.changeOrigin x k‖ ≤ 2 * C * (2 / r) ^ k := by
  have hr' : (0 : ℝ) < r := hr
  have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ ‖p 0‖ * (r : ℝ) ^ 0).trans (hC 0)
  have hterm : ∀ l : ℕ,
      ‖p.changeOriginSeries k l (fun _ => x)‖ ≤ C * (2 / (r : ℝ)) ^ k * (1 / 2) ^ l := by
    intro l
    have hp : ‖p (k + l)‖ ≤ C / (r : ℝ) ^ (k + l) := by
      rw [le_div_iff₀ (pow_pos hr' _)]
      exact hC _
    calc ‖p.changeOriginSeries k l (fun _ => x)‖
        ≤ 2 ^ (k + l) * ‖p (k + l)‖ * ‖x‖ ^ l := norm_changeOriginSeries_apply_le p k l x
      _ ≤ 2 ^ (k + l) * (C / (r : ℝ) ^ (k + l)) * ((r : ℝ) / 4) ^ l := by gcongr
      _ = C * (2 / (r : ℝ)) ^ k * ((2 / (r : ℝ)) * ((r : ℝ) / 4)) ^ l := by
          rw [mul_pow, div_pow 2 (r : ℝ) k, div_pow 2 (r : ℝ) l, pow_add, pow_add]
          field_simp
      _ = C * (2 / (r : ℝ)) ^ k * (1 / 2) ^ l := by
          rw [show (2 / (r : ℝ)) * ((r : ℝ) / 4) = 1 / 2 by field_simp; norm_num]
  have hsum : HasSum (fun l : ℕ => C * (2 / (r : ℝ)) ^ k * (1 / 2) ^ l)
      (C * (2 / (r : ℝ)) ^ k * 2) :=
    hasSum_geometric_two.mul_left _
  calc ‖p.changeOrigin x k‖ = ‖∑' l, p.changeOriginSeries k l (fun _ => x)‖ := rfl
    _ ≤ C * (2 / (r : ℝ)) ^ k * 2 := tsum_of_norm_bounded hsum hterm
    _ = 2 * C * (2 / r) ^ k := by ring

/-- A function that is real analytic at `x₀` has factorial bounds for all its derivatives,
uniformly on a ball around `x₀`. -/
theorem exists_ball_hasFactorialDerivativeBoundsOn_of_analyticAt [CompleteSpace F]
    {f : E → F} {x₀ : E} (hf : AnalyticAt ℝ f x₀) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 < A ∧
      HasFactorialDerivativeBoundsOn f (Metric.ball x₀ R) C A := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hρpos : 0 < ρ := by exact_mod_cast hρ0
  have hρpos' : (0 : ℝ) < ρ := hρpos
  obtain ⟨C, hC0, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hρr.trans_le hp.r_le)
  refine ⟨ρ / 4, by positivity, 2 * C, by positivity, 2 / ρ, by positivity, ?_⟩
  intro y hy j
  have hz_le : ‖y - x₀‖ ≤ ρ / 4 := by
    have := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at this
    exact this.le
  have hzr : (‖y - x₀‖₊ : ℝ≥0∞) < r := by
    refine lt_of_le_of_lt ?_ hρr
    have : ‖y - x₀‖₊ ≤ ρ := by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      linarith
    exact_mod_cast this
  have hq := hp.changeOrigin hzr
  rw [add_sub_cancel] at hq
  calc ‖iteratedFDeriv ℝ j f y‖ ≤ (j.factorial : ℝ) * ‖p.changeOrigin (y - x₀) j‖ :=
        norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hq j
    _ ≤ (j.factorial : ℝ) * (2 * C * (2 / (ρ : ℝ)) ^ j) := by
        gcongr
        exact norm_changeOrigin_le p hρpos hC hz_le j
    _ = 2 * C * (2 / (ρ : ℝ)) ^ j * (j.factorial : ℝ) := by ring

/-- The same bounds on a ball of radius at most a prescribed `R₀ > 0`, on which `f` is moreover
analytic. -/
theorem exists_ball_le_hasFactorialDerivativeBoundsOn_of_analyticAt [CompleteSpace F]
    {f : E → F} {x₀ : E} (hf : AnalyticAt ℝ f x₀) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ R : ℝ, 0 < R ∧ R ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 < A ∧
      AnalyticOnNhd ℝ f (Metric.ball x₀ R) ∧
      HasFactorialDerivativeBoundsOn f (Metric.ball x₀ R) C A := by
  obtain ⟨R, hR, C, hC, A, hA, hb⟩ := exists_ball_hasFactorialDerivativeBoundsOn_of_analyticAt hf
  obtain ⟨ε, hε, hεan⟩ := Metric.eventually_nhds_iff_ball.1 hf.eventually_analyticAt
  refine ⟨min (min R ε) R₀, lt_min (lt_min hR hε) hR₀, min_le_right _ _, C, hC, A, hA, ?_, ?_⟩
  · intro y hy
    exact hεan y (Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hy)
  · exact hb.mono (Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)))

namespace CoordinateScalarOperator

variable {d r : ℕ}

/-- The coefficients of a coordinate scalar operator that are analytic near `x₀ ∈ S` have
factorial derivative bounds with one common ball, of radius at most `R₀`, and common
constants `C`, `A` for all orders `k ≤ r` and all words `w`. -/
theorem AnalyticCoefficientsOn.exists_ball_hasFactorialDerivativeBoundsOn
    {D : CoordinateScalarOperator E d r} {S : Set E} (hD : D.AnalyticCoefficientsOn S)
    {x₀ : E} (hx₀ : x₀ ∈ S) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ R : ℝ, 0 < R ∧ R ≤ R₀ ∧ ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 < A ∧
      ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
        AnalyticOnNhd ℝ (D.coefficient k w) (Metric.ball x₀ R) ∧
        HasFactorialDerivativeBoundsOn (D.coefficient k w) (Metric.ball x₀ R) C A := by
  have h := fun i : (Σ k : Fin (r + 1), (Fin k.val → Fin d)) =>
    exists_ball_le_hasFactorialDerivativeBoundsOn_of_analyticAt (hD i.1 i.2 x₀ hx₀) hR₀
  choose R hR hRle C hC A hA han hb using h
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ i, y ∈ Metric.ball x₀ (R i) :=
    Filter.eventually_all.2 fun i => Metric.ball_mem_nhds x₀ (hR i)
  obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hCpos : 0 < 1 + ∑ i, C i :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (hC i).le)
  have hApos : 0 < 1 + ∑ i, A i :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (hA i).le)
  refine ⟨min ε R₀, lt_min hε hR₀, min_le_right _ _, 1 + ∑ i, C i, hCpos,
    1 + ∑ i, A i, hApos, fun k w => ?_⟩
  have hsub : Metric.ball x₀ (min ε R₀) ⊆ Metric.ball x₀ (R ⟨k, w⟩) := fun y hy =>
    hεsub y (Metric.ball_subset_ball (min_le_left _ _) hy) ⟨k, w⟩
  refine ⟨(han ⟨k, w⟩).mono hsub, ((hb ⟨k, w⟩).mono hsub).mono_const (hA ⟨k, w⟩).le ?_ ?_⟩
  · exact le_add_of_nonneg_of_le zero_le_one
      (Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ _))
  · exact le_add_of_nonneg_of_le zero_le_one
      (Finset.single_le_sum (fun i _ => (hA i).le) (Finset.mem_univ _))

end CoordinateScalarOperator

end Langlands.Analysis

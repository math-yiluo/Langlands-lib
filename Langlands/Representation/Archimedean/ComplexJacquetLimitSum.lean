import Langlands.Representation.Archimedean.ComplexJacquetLimit

/-!
# The limit argument along `P_{m,1}` for finite sums, with the hypothesis on a ray

`ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero` shows: if `∫_{U(m+1)} u(κ g) h(κ) dκ = 0`
for every `g`, then `∫_{U(m)} u(ι(k)) (T h)(k) dk = 0`, where `T` is the partial Jacquet integral.
Its proof uses the hypothesis only at the diagonal matrices `g = diag(1, …, 1, s)`. This file
proves the same for a finite family of pairs `(u_i, h_i)`, assuming only
`∑_i ∫_{U(m+1)} u_i(κ d(s)) h_i(κ) dκ = 0` for every `s ∈ ℂˣ`, where `d(s) = diag(1, …, 1, s)`
(`ComplexJacquetLimitSum.sum_integral_mul_jacquetStep_eq_zero`). The case of two pairs is an
identity (`ComplexJacquetLimitSum.integral_mul_jacquetStep_eq_of_ray`).
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexJacquetLimitSum

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexPartialJacquet
  ComplexGramFormula Langlands.GeneralLinear ComplexDuality ComplexKIntegralInvariance
  ComplexJacquetLimit

variable {m : ℕ}

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The integrand `u(J(x/s, 1) ι(k)) h(J(x, 1) ι(k))` of the limit argument. -/
def rayΦ (u h : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (s : ℝ)
    (p : unitaryCompact ℂ m × (Fin m → ℂ)) : ℂ :=
  u (chartGL (((s : ℂ))⁻¹ • p.2) * iotaGL (p.1 : Langlands.GeneralLinear m ℂ)) *
    h (chartGL p.2 * iotaGL (p.1 : Langlands.GeneralLinear m ℂ))

/-- The double integral `∫_{U(m)} ∫_{ℂ^m} u(J(x/s, 1) ι(k)) h(J(x, 1) ι(k)) dx dk`. -/
def rayIntegral (u h : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (s : ℝ) : ℂ :=
  ∫ k : unitaryCompact ℂ m, (∫ x, rayΦ u h s (k, x)) ∂unitaryHaar m

/-- The value of the principal series character of `χ⁻¹` at `d(s) = diag(1, …, 1, s)`. -/
def rayConstant (χ : ℕ → ℂˣ → ℂ) (m : ℕ) (s : ℂˣ) : ℂ :=
  principalSeriesCharacter ℂ (m + 1) (dualChar χ) (fun i => Fin.lastCases s (fun _ => 1) i)

theorem continuous_rayΦ {u h : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hu : Continuous u)
    (hh : Continuous h) (s : ℝ) : Continuous (rayΦ u h s) := by
  have hk : Continuous fun p : unitaryCompact ℂ m × (Fin m → ℂ) =>
      iotaGL (p.1 : Langlands.GeneralLinear m ℂ) :=
    continuous_iotaGL.comp (continuous_subtype_val.comp continuous_fst)
  have h1 : Continuous fun p : unitaryCompact ℂ m × (Fin m → ℂ) =>
      chartGL (((s : ℂ))⁻¹ • p.2) :=
    continuous_chartGL.comp (continuous_snd.const_smul ((s : ℂ))⁻¹)
  have h2 : Continuous fun p : unitaryCompact ℂ m × (Fin m → ℂ) => chartGL p.2 :=
    continuous_chartGL.comp continuous_snd
  exact (hu.comp (h1.mul hk)).mul (hh.comp (h2.mul hk))

theorem rayConstant_ne_zero (hχ : IsPhasePower χ e) (s : ℂˣ) : rayConstant χ m s ≠ 0 := by
  rw [← norm_ne_zero_iff, rayConstant, norm_principalSeriesCharacter hχ.dual]
  exact (Finset.prod_pos fun l _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (Units.ne_zero _)) _).ne'

/-- **The pairing identity along the ray.** For `s > 0`,
`∫_{U(m+1)} u(κ d(s)) h(κ) dκ = c_m χ⁻¹(d(s)) ∫_{U(m)} ∫_{ℂ^m} u(J(x/s,1) ι(k)) h(J(x,1) ι(k))`. -/
theorem integral_mul_dlastGL_eq (hχ : IsPhasePower χ e)
    {u h : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (m + 1) (dualChar χ)) (hh : h ∈ principalSeries ℂ (m + 1) χ)
    (s : ℝ) (s' : ℂˣ) (hs' : (s' : ℂ) = s) :
    ∫ κ, u ((κ : Langlands.GeneralLinear (m + 1) ℂ) * dlastGL s') * h κ
        ∂unitaryHaar (m + 1) =
      (chartConstant m : ℂ) * (rayConstant χ m s' * rayIntegral u h s) := by
  have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu (dlastGL s')
  set F : Langlands.GeneralLinear (m + 1) ℂ → ℂ :=
    fun y => u (y * dlastGL s') * h y with hFdef
  have hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1)) := by
    refine ⟨contMDiff_mul_fun hud.1 hh.1, fun a v y => ?_⟩
    simp only [hFdef]
    rw [mul_assoc _ y, hu.2 a v, hh.2 a v y, ← principalSeriesCharacter_dual_mul hχ]
    ring
  have h1 := integral_eq_chart' hF
  have hpt : ∀ (k : unitaryCompact ℂ m) (x : Fin m → ℂ),
      F (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℂ)) =
        rayConstant χ m s' * rayΦ u h s (k, x) := by
    intro k x
    simp only [hFdef, rayΦ, rayConstant]
    rw [mul_assoc, iotaGL_mul_dlastGL, ← mul_assoc, chartGL_mul_dlastGL, mul_assoc,
      apply_dlastGL_mul hu, hs']
    ring
  simp_rw [hpt, integral_const_mul] at h1
  exact h1

/-- **The limit of the double integrals.** For strictly dominant `χ`,
`rayIntegral u h (n + 1) → ∫_{U(m)} u(ι(k)) (T h)(k) dk` (dominated convergence; no vanishing
hypothesis). -/
theorem tendsto_rayIntegral (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    {u h : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (m + 1) (dualChar χ)) (hh : h ∈ principalSeries ℂ (m + 1) χ) :
    Tendsto (fun n : ℕ => rayIntegral u h ((n : ℝ) + 1)) atTop
      (𝓝 (∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep h k
        ∂unitaryHaar m)) := by
  have hΦc : ∀ s, Continuous (rayΦ u h s) := continuous_rayΦ hu.1.continuous hh.1.continuous
  obtain ⟨Cu, hCu⟩ := exists_bound_unitaryCompact hu.1.continuous
  obtain ⟨Ch, hCh⟩ := exists_bound_unitaryCompact hh.1.continuous
  have hCu0 : 0 ≤ Cu := le_trans (norm_nonneg _) (hCu 1 (unitaryCompact ℂ (m + 1)).one_mem)
  have hCh0 : 0 ≤ Ch := le_trans (norm_nonneg _) (hCh 1 (unitaryCompact ℂ (m + 1)).one_mem)
  set γ : Fin m → ℝ := fun l => max (chartExponent e l) (-2) with hγdef
  have hγ : ∀ l, γ l < -1 := fun l => max_lt (chartExponent_lt he l) (by norm_num)
  set D : (Fin m → ℂ) → ℝ := fun x => Cu * Ch * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ γ l with hDdef
  have hDi : Integrable D := (integrable_prod_one_add_sq_rpow hγ).const_mul _
  have hbound : ∀ s : ℝ, 1 ≤ s → ∀ (k : unitaryCompact ℂ m) (x : Fin m → ℂ),
      ‖rayΦ u h s (k, x)‖ ≤ D x := by
    intro s hs k x
    simp only [rayΦ, hDdef]
    rw [norm_mul]
    have hk := iotaGL_mem_unitaryCompact k.2
    have h1 := norm_le_partialSq hχ.dual hu hCu (((s : ℂ))⁻¹ • x) hk
    have h2 := norm_le_partialSq hχ hh hCh x hk
    have hsum : ∀ l : Fin m, chartExponent (fun l => -e l) l + chartExponent e l = -2 := by
      intro l
      unfold chartExponent
      simp only [Complex.neg_re]
      ring
    have hneg : ∀ l : Fin m, chartExponent e l < 0 := fun l => by
      linarith [chartExponent_lt he l]
    have habs : ‖((s : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact inv_le_one_of_one_le₀ hs
    have hd := prod_rpow_mul_prod_rpow_le (x := x) habs hsum hneg
    have hp1 : 0 ≤ ∏ l : Fin m, partialSq (((s : ℂ))⁻¹ • x) ((l : ℕ) + 1) ^
        chartExponent (fun l => -e l) l :=
      Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le
    calc ‖u (chartGL (((s : ℂ))⁻¹ • x) * iotaGL (k : Langlands.GeneralLinear m ℂ))‖ *
          ‖h (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℂ))‖
        ≤ (Cu * ∏ l : Fin m, partialSq (((s : ℂ))⁻¹ • x) ((l : ℕ) + 1) ^
            chartExponent (fun l => -e l) l) *
          (Ch * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCu0 hp1)
      _ = Cu * Ch * ((∏ l : Fin m, partialSq (((s : ℂ))⁻¹ • x) ((l : ℕ) + 1) ^
            chartExponent (fun l => -e l) l) *
          ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l) := by ring
      _ ≤ Cu * Ch * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ γ l :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hCu0 hCh0)
  have hn1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  refine tendsto_integral_of_dominated_convergence (fun _ => ∫ x, D x)
    (fun n => (hΦc _).aestronglyMeasurable.integral_prod_right') (integrable_const _)
    (fun n => ae_of_all _ fun k => ?_) (ae_of_all _ fun k => ?_)
  · exact norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound _ (hn1 n) k))
  · have heq : u (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep h k =
        ∫ x, u (iotaGL (k : Langlands.GeneralLinear m ℂ)) *
          h (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℂ)) := by
      rw [jacquetStep, integral_const_mul]
    rw [heq]
    refine tendsto_integral_of_dominated_convergence D
      (fun n => ((hΦc _).comp
        (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
      hDi (fun n => ae_of_all _ (hbound _ (hn1 n) k)) (ae_of_all _ fun x => ?_)
    have hs : Tendsto (fun n : ℕ => ((((n : ℝ) + 1 : ℝ) : ℂ))⁻¹ • x) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun n : ℕ => ((((n : ℝ) + 1 : ℝ) : ℂ))⁻¹) atTop (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp h0
        simpa [Function.comp_def, one_div] using this
      simpa using h1.smul_const x
    have hcont : Continuous fun y : Fin m → ℂ =>
        u (chartGL y * iotaGL (k : Langlands.GeneralLinear m ℂ)) :=
      hu.1.continuous.comp (continuous_chartGL.mul continuous_const)
    have h2 := (hcont.tendsto 0).comp hs
    simp only [Function.comp_def, chartGL_zero, one_mul] at h2
    exact h2.mul_const _

/-- **The limit argument along `P_{m,1}` for finite sums, hypothesis on the ray.** Let `u_i` lie
in the principal series of `χ⁻¹` and `h_i` in that of a strictly dominant `χ`. If
`∑_i ∫_{U(m+1)} u_i(κ d(s)) h_i(κ) dκ = 0` for every `s ∈ ℂˣ`, where `d(s) = diag(1, …, 1, s)`,
then `∑_i ∫_{U(m)} u_i(ι(k)) (T h_i)(k) dk = 0`. -/
theorem sum_integral_mul_jacquetStep_eq_zero (hχ : IsPhasePower χ e)
    (he : IsStrictlyDominant e m) {ι : Type*} (S : Finset ι)
    {u h : ι → Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hu : ∀ i ∈ S, u i ∈ principalSeries ℂ (m + 1) (dualChar χ))
    (hh : ∀ i ∈ S, h i ∈ principalSeries ℂ (m + 1) χ)
    (h0 : ∀ s : ℂˣ, ∑ i ∈ S, ∫ κ, u i ((κ : Langlands.GeneralLinear (m + 1) ℂ) * dlastGL s) *
      h i κ ∂unitaryHaar (m + 1) = 0) :
    ∑ i ∈ S, ∫ k, u i (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep (h i) k
      ∂unitaryHaar m = 0 := by
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ S, rayIntegral (u i) (h i) ((n : ℝ) + 1)) atTop
      (𝓝 (∑ i ∈ S, ∫ k, u i (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep (h i) k
        ∂unitaryHaar m)) :=
    tendsto_finsetSum S fun i hi => tendsto_rayIntegral hχ he (hu i hi) (hh i hi)
  have hzero : ∀ n : ℕ, ∑ i ∈ S, rayIntegral (u i) (h i) ((n : ℝ) + 1) = 0 := by
    intro n
    have hs0 : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (0 : ℝ) < (n : ℝ) + 1 by positivity).ne'
    set s' : ℂˣ := Units.mk0 (((n : ℝ) + 1 : ℝ) : ℂ) hs0
    have h2 := h0 s'
    rw [Finset.sum_congr rfl fun i hi =>
      integral_mul_dlastGL_eq hχ (hu i hi) (hh i hi) ((n : ℝ) + 1) s' (Units.val_mk0 _),
      ← Finset.mul_sum, ← Finset.mul_sum] at h2
    have hc : (chartConstant m : ℂ) ≠ 0 := by exact_mod_cast (chartConstant_pos m).ne'
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hc
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 (rayConstant_ne_zero hχ s')
      · exact h4
  simp only [hzero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm

/-- **Identity form.** If two matrix-coefficient integrals agree along the ray
`d(s) = diag(1, …, 1, s)`, then so do their partial Jacquet pairings. -/
theorem integral_mul_jacquetStep_eq_of_ray (hχ : IsPhasePower χ e)
    (he : IsStrictlyDominant e m) {u₁ h₁ u₂ h₂ : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hu₁ : u₁ ∈ principalSeries ℂ (m + 1) (dualChar χ))
    (hh₁ : h₁ ∈ principalSeries ℂ (m + 1) χ)
    (hu₂ : u₂ ∈ principalSeries ℂ (m + 1) (dualChar χ))
    (hh₂ : h₂ ∈ principalSeries ℂ (m + 1) χ)
    (heq : ∀ s : ℂˣ,
      ∫ κ, u₁ ((κ : Langlands.GeneralLinear (m + 1) ℂ) * dlastGL s) * h₁ κ
        ∂unitaryHaar (m + 1) =
      ∫ κ, u₂ ((κ : Langlands.GeneralLinear (m + 1) ℂ) * dlastGL s) * h₂ κ
        ∂unitaryHaar (m + 1)) :
    ∫ k, u₁ (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep h₁ k ∂unitaryHaar m =
      ∫ k, u₂ (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep h₂ k ∂unitaryHaar m := by
  have hneg : -u₂ ∈ principalSeries ℂ (m + 1) (dualChar χ) :=
    (principalSeries ℂ (m + 1) (dualChar χ)).neg_mem hu₂
  have h := sum_integral_mul_jacquetStep_eq_zero hχ he (Finset.univ : Finset Bool)
    (u := fun b => if b then u₁ else -u₂) (h := fun b => if b then h₁ else h₂)
    (fun b _ => by cases b <;> simpa) (fun b _ => by cases b <;> simpa) (fun s => by
      simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton, Pi.neg_apply,
        neg_mul, integral_neg, heq s]
      ring)
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton, Pi.neg_apply,
    neg_mul, integral_neg] at h
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact h)

end ComplexJacquetLimitSum

end Langlands.Archimedean

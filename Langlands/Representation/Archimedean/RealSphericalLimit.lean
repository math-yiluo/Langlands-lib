import Langlands.Representation.Archimedean.RealSphericalChart
import Langlands.Representation.Archimedean.JacquetLimit

/-!
# The limit argument for the regularized vector

Let `χ` be a signed-power character with exponents `e` and trivial signs on `GL_{m+1}(ℝ)`, whose
real parts weakly decrease, and let `H` be the regularized vector of the principal series of `χ`.
If `u` lies in the principal series of `χ⁻¹` and `∫_{O(m+1)} u(κ g) H(κ) dκ = 0` for every `g`,
then `∫_{O(m)} u(ι(k)) dk = 0`.

The proof is the limit argument of `JacquetLimit.integral_mul_jacquetStep_eq_zero` with `h = H`:
only the domination changes, because the exponents are only weakly dominant. The extra factor
`r_m(x)^{-1}` of `H` along the chart makes the dominating function integrable.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealSphericalLimit

open MaximalParabolicIntegration ParabolicChartBound PartialJacquet GramFormula
  Langlands.GeneralLinear RealPrincipalSeriesDuality JacquetLimit RealSphericalChart
  PartialSqIntegral JacquetNonvanishing

attribute [local instance] measurableSpaceK

local instance borelSpaceK_rsl (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {m : ℕ}

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- Per-factor domination for a dual pair with weakly dominant exponents. -/
theorem prod_rpow_mul_prod_rpow_le_half {x : Fin m → ℝ} {s : ℝ} (hs : |s| ≤ 1)
    {εu εh : Fin m → ℝ} (hsum : ∀ l, εu l + εh l = -1) (hle : ∀ l, εh l ≤ -1 / 2) :
    (∏ l : Fin m, partialSq (s • x) ((l : ℕ) + 1) ^ εu l) *
        ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ εh l ≤
      ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ (-1 / 2 : ℝ) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun l _ => mul_nonneg
    (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le
    (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le) fun l _ => ?_
  set A := partialSq (s • x) ((l : ℕ) + 1)
  set B := partialSq x ((l : ℕ) + 1)
  have hA : 1 ≤ A := one_le_partialSq _ _
  have hB : 1 ≤ B := one_le_partialSq _ _
  have hAB : A ≤ B := partialSq_smul_le hs x _
  by_cases hu : 0 ≤ εu l
  · calc A ^ εu l * B ^ εh l ≤ B ^ εu l * B ^ εh l :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hAB hu)
            (Real.rpow_pos_of_pos (by linarith) _).le
      _ = B ^ (-1 : ℝ) := by rw [← Real.rpow_add (by linarith), hsum l]
      _ ≤ B ^ (-1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
  · calc A ^ εu l * B ^ εh l ≤ 1 * B ^ εh l :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith))
            (Real.rpow_pos_of_pos (by linarith) _).le
      _ = B ^ εh l := one_mul _
      _ ≤ B ^ (-1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB (hle l)

/-- The tail condition for the dominating function. -/
theorem tailCondition_half : TailCondition (fun _ : Fin m => (-1 / 2 : ℂ)) (-1) := by
  intro j
  have h0 : ∀ l : Fin m, (if j ≤ l then ((-1 / 2 : ℂ)).re + 1 / 2 else 0) = 0 := by
    intro l
    split_ifs <;> norm_num
  simp only [h0, Finset.sum_const_zero]
  norm_num

theorem norm_partialSqProd_half (x : Fin m → ℝ) :
    ‖partialSqProd (fun _ : Fin m => (-1 / 2 : ℂ)) (-1) x‖ =
      partialSq x m ^ (-1 : ℝ) * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ (-1 / 2 : ℝ) := by
  rw [norm_partialSqProd]
  norm_num

/-- **The limit argument for the regularized vector.** -/
theorem integral_iota_eq_zero (hχ : IsSignedPower χ e) (hp : ∀ l, χ l (-1) = 1)
    (he : IsWeaklyDominant e m)
    {u : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hu : u ∈ principalSeries ℝ (m + 1) (dualChar χ))
    (h0 : ∀ g : Langlands.GeneralLinear (m + 1) ℝ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (m + 1) ℝ) * g) *
        signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1) κ ∂haarK (m + 1) = 0) :
    ∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℝ)) ∂haarK m = 0 := by
  set h : Langlands.GeneralLinear (m + 1) ℝ → ℂ :=
    signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1) with hhdef
  have hh : h ∈ principalSeries ℝ (m + 1) χ :=
    (signVector_mem (n := m + 1) (fun _ => 0) (bump (fun _ => 0) m 1) hχ (sign_zero hp)).1
  set Φ : ℝ → unitaryCompact ℝ m × (Fin m → ℝ) → ℂ := fun s p =>
    u (chartGL (s⁻¹ • p.2) * iotaGL (p.1 : Langlands.GeneralLinear m ℝ)) *
      h (chartGL p.2 * iotaGL (p.1 : Langlands.GeneralLinear m ℝ)) with hΦ
  have hΦc : ∀ s, Continuous (Φ s) := by
    intro s
    have hk : Continuous fun p : unitaryCompact ℝ m × (Fin m → ℝ) =>
        iotaGL (p.1 : Langlands.GeneralLinear m ℝ) :=
      continuous_iotaGL.comp (continuous_subtype_val.comp continuous_fst)
    have h1 : Continuous fun p : unitaryCompact ℝ m × (Fin m → ℝ) => chartGL (s⁻¹ • p.2) :=
      continuous_chartGL.comp (continuous_snd.const_smul s⁻¹)
    have h2 : Continuous fun p : unitaryCompact ℝ m × (Fin m → ℝ) => chartGL p.2 :=
      continuous_chartGL.comp continuous_snd
    simp only [hΦ]
    exact (hu.1.continuous.comp (h1.mul hk)).mul (hh.1.continuous.comp (h2.mul hk))
  -- the pairing identity
  have hI : ∀ s : ℝ, 0 < s → ∫ k : unitaryCompact ℝ m, (∫ x, Φ s (k, x)) ∂haarK m = 0 := by
    intro s hs
    have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu
      (dlastGL (Units.mk0 s hs.ne'))
    set F : Langlands.GeneralLinear (m + 1) ℝ → ℂ :=
      fun y => u (y * dlastGL (Units.mk0 s hs.ne')) * h y with hFdef
    have hFs : ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ F := contMDiff_mul_fun hud.1 hh.1
    have hF : IsModulusCovariant F := by
      intro a v y
      simp only [hFdef]
      rw [mul_assoc _ y, hu.2 a v, hh.2 a v y, ← principalSeriesCharacter_dual_mul hχ]
      ring
    have h1 := integral_eq_chart' hFs hF
    rw [show (∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1)) = 0 from
      h0 _] at h1
    set c' := principalSeriesCharacter ℝ (m + 1) (dualChar χ)
      (fun i => Fin.lastCases (Units.mk0 s hs.ne') (fun _ => 1) i) with hc'def
    have hpt : ∀ (k : unitaryCompact ℝ m) (x : Fin m → ℝ),
        F (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℝ)) = c' * Φ s (k, x) := by
      intro k x
      simp only [hFdef, hΦ]
      rw [mul_assoc, iotaGL_mul_dlastGL, ← mul_assoc, chartGL_mul_dlastGL, mul_assoc,
        apply_dlastGL_mul hu, Units.val_mk0]
      ring
    simp_rw [hpt, integral_const_mul] at h1
    have hc : (chartConstant m : ℂ) ≠ 0 := by exact_mod_cast (chartConstant_pos m).ne'
    have hc' : c' ≠ 0 := by
      rw [← norm_ne_zero_iff, hc'def, norm_principalSeriesCharacter hχ.dual]
      exact (Finset.prod_pos fun l _ =>
        Real.rpow_pos_of_pos (abs_pos.mpr (Units.ne_zero _)) _).ne'
    have h2 := h1.symm
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hc
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hc'
      · exact h4
  -- the domination
  obtain ⟨Cu, hCu⟩ := exists_bound_unitaryCompact hu.1.continuous
  have hCu0 : 0 ≤ Cu := le_trans (norm_nonneg _) (hCu 1 (unitaryCompact ℝ (m + 1)).one_mem)
  set D : (Fin m → ℝ) → ℝ :=
    fun x => Cu * ‖partialSqProd (fun _ : Fin m => (-1 / 2 : ℂ)) (-1) x‖ with hDdef
  have hDi : Integrable D :=
    (integrable_and_integral_ne_zero m _ _ tailCondition_half).1.norm.const_mul _
  have hbound : ∀ s : ℝ, 1 ≤ s → ∀ (k : unitaryCompact ℝ m) (x : Fin m → ℝ),
      ‖Φ s (k, x)‖ ≤ D x := by
    intro s hs k x
    simp only [hΦ, hDdef]
    rw [norm_mul, hhdef, regularized_chart hχ hp x k.2, norm_partialSqProd_chartDiff,
      norm_partialSqProd_half]
    have hk := iotaGL_mem_unitaryCompact k.2
    have h1 := norm_le_partialSq hχ.dual hu hCu (s⁻¹ • x) hk
    have hsum : ∀ l : Fin m, chartExponent (fun l => -e l) l + chartExponent e l = -1 := by
      intro l
      unfold chartExponent
      simp only [Complex.neg_re]
      ring
    have hle : ∀ l : Fin m, chartExponent e l ≤ -1 / 2 := fun l => by
      have := he l l.isLt
      unfold chartExponent
      linarith
    have habs : |s⁻¹| ≤ 1 := by
      rw [abs_inv, abs_of_pos (by linarith)]
      exact inv_le_one_of_one_le₀ hs
    have hd := prod_rpow_mul_prod_rpow_le_half (x := x) habs hsum hle
    have hp1 : 0 ≤ ∏ l : Fin m, partialSq (s⁻¹ • x) ((l : ℕ) + 1) ^
        chartExponent (fun l => -e l) l :=
      Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le
    have hr : 0 ≤ partialSq x m ^ (-1 : ℝ) := (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le
    calc ‖u (chartGL (s⁻¹ • x) * iotaGL (k : Langlands.GeneralLinear m ℝ))‖ *
          (partialSq x m ^ (-1 : ℝ) *
            ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l)
        ≤ (Cu * ∏ l : Fin m, partialSq (s⁻¹ • x) ((l : ℕ) + 1) ^
            chartExponent (fun l => -e l) l) *
          (partialSq x m ^ (-1 : ℝ) *
            ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hr
            (Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le))
      _ = Cu * partialSq x m ^ (-1 : ℝ) * ((∏ l : Fin m, partialSq (s⁻¹ • x) ((l : ℕ) + 1) ^
            chartExponent (fun l => -e l) l) *
          ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l) := by ring
      _ ≤ Cu * partialSq x m ^ (-1 : ℝ) *
            ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ (-1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hCu0 hr)
      _ = Cu * (partialSq x m ^ (-1 : ℝ) *
            ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ (-1 / 2 : ℝ)) := by ring
  have hn1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  -- the limit
  have hlim : Tendsto (fun n : ℕ => ∫ k : unitaryCompact ℝ m,
      (∫ x, Φ ((n : ℝ) + 1) (k, x)) ∂haarK m) atTop
      (𝓝 (∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℝ)) * jacquetStep h k ∂haarK m)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ∫ x, D x)
      (fun n => (hΦc _).aestronglyMeasurable.integral_prod_right') (integrable_const _)
      (fun n => ae_of_all _ fun k => ?_) (ae_of_all _ fun k => ?_)
    · exact norm_integral_le_of_norm_le hDi (ae_of_all _ (hbound _ (hn1 n) k))
    · have heq : u (iotaGL (k : Langlands.GeneralLinear m ℝ)) * jacquetStep h k =
          ∫ x, u (iotaGL (k : Langlands.GeneralLinear m ℝ)) *
            h (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℝ)) := by
        rw [jacquetStep, integral_const_mul]
      rw [heq]
      refine tendsto_integral_of_dominated_convergence D
        (fun n => ((hΦc _).comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
        hDi (fun n => ae_of_all _ (hbound _ (hn1 n) k)) (ae_of_all _ fun x => ?_)
      have hs : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa only [one_div] using h0
        simpa using h1.smul_const x
      have hcont : Continuous fun y : Fin m → ℝ =>
          u (chartGL y * iotaGL (k : Langlands.GeneralLinear m ℝ)) :=
        hu.1.continuous.comp (continuous_chartGL.mul continuous_const)
      have h2 := (hcont.tendsto 0).comp hs
      simp only [Function.comp_def, chartGL_zero, one_mul] at h2
      exact h2.mul_const _
  have hzero : ∀ n : ℕ, ∫ k : unitaryCompact ℝ m, (∫ x, Φ ((n : ℝ) + 1) (k, x)) ∂haarK m = 0 :=
    fun n => hI _ (by linarith [hn1 n])
  simp only [hzero] at hlim
  have hpair := tendsto_nhds_unique hlim tendsto_const_nhds
  have hconst : ∀ k : unitaryCompact ℝ m,
      u (iotaGL (k : Langlands.GeneralLinear m ℝ)) * jacquetStep h k =
        u (iotaGL (k : Langlands.GeneralLinear m ℝ)) *
          ∫ x, partialSqProd (chartDiff (m := m) e) (-1) x := fun k => by
    rw [hhdef, jacquetStep_regularized hχ hp k.2]
  simp_rw [hconst, integral_mul_const] at hpair
  rcases mul_eq_zero.mp hpair with h3 | h3
  · exact h3
  · exact absurd h3 (integral_regularized_ne_zero he).2

end RealSphericalLimit

end Langlands.Archimedean

import Langlands.Representation.Archimedean.PartialJacquetIntegral

/-!
# The limit argument along the maximal parabolic subgroup `P_{m,1}`
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace JacquetLimit

open MaximalParabolicIntegration ParabolicChartBound PartialJacquet GramFormula
  Langlands.GeneralLinear RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK_jl (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {m : ℕ}

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

theorem principalSeriesCharacter_dual_mul (hχ : IsSignedPower χ e) (N : ℕ) (a : Fin N → ℝˣ) :
    principalSeriesCharacter ℝ N (dualChar χ) a * principalSeriesCharacter ℝ N χ a =
      modulusCharacter N a := by
  unfold principalSeriesCharacter modulusCharacter
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs, dualChar]
  have hx : ((|(a i : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (a i).ne_zero
  have hc := hχ.ne_zero i (a i)
  rw [show (χ i (a i))⁻¹ * ((|(a i : ℝ)| : ℝ) : ℂ) ^ (((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
      (χ i (a i) * ((|(a i : ℝ)| : ℝ) : ℂ) ^ (((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) =
      ((χ i (a i))⁻¹ * χ i (a i)) * (((|(a i : ℝ)| : ℝ) : ℂ) ^ (((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((|(a i : ℝ)| : ℝ) : ℂ) ^ (((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) by ring,
    inv_mul_cancel₀ hc, one_mul, ← Complex.cpow_add _ _ hx]
  congr 1
  ring

theorem norm_modulusCharacter (n : ℕ) (a : Fin n → ℝˣ) :
    ‖modulusCharacter n a‖ = ∏ l : Fin n, |(a l : ℝ)| ^ ((n : ℝ) - 1 - 2 * ((l : ℕ) : ℝ)) := by
  rw [modulusCharacter, norm_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr (a l).ne_zero)]
  congr 1
  simp

/-! ## The integration formula with the compact variable outside -/

theorem norm_le_of_covariant {F : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hF : IsModulusCovariant F) {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ (m + 1), ‖F k‖ ≤ C)
    (x : Fin m → ℝ) {κ : Langlands.GeneralLinear (m + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    ‖F (chartGL x * κ)‖ ≤ C * ∏ l : Fin m, (1 + x l ^ 2) ^ (-1 : ℝ) := by
  set σ : ℕ → ℝ := fun l => ((m + 1 : ℕ) : ℝ) - 1 - 2 * (l : ℝ) with hσ
  have hb := norm_le_chart (σ := σ) hF (norm_modulusCharacter (m + 1)) hC x hκ
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℝ (m + 1)).one_mem)
  have hexp : ∀ l : Fin m, (σ ((l : ℕ) + 1) - σ l) / 2 = -1 := by
    intro l
    simp only [hσ]
    push_cast
    ring
  simp only [hexp] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (prod_partialSq_rpow_le fun _ => by norm_num) hC0)

theorem iotaGL_mul_chartGL (k : Langlands.GeneralLinear m ℝ) (v : Fin m → ℝ) :
    iotaGL k * chartGL v =
      chartGL (v ᵥ* ((k⁻¹ : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ)) * iotaGL k := by
  rw [chartGL_mul_iotaGL, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    vecMul_one]

theorem det_inv_ne_zero (k : Langlands.GeneralLinear m ℝ) :
    ((k⁻¹ : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero

/-- **The integration formula, compact variable outside.**
`∫_{O(m+1)} F = c_m ∫_{O(m)} ∫_{ℝ^m} F(J(x,1) ι(k)) dx dk`. -/
theorem integral_eq_chart' {F : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hFs : ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ F) (hF : IsModulusCovariant F) :
    ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) =
      (chartConstant m : ℂ) * ∫ k : unitaryCompact ℝ m,
        (∫ x : Fin m → ℝ, F (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℝ))) ∂haarK m := by
  rw [integral_eq_chart hFs hF]
  congr 1
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hFs.continuous
  set D : (Fin m → ℝ) → ℝ := fun x => C * ∏ l : Fin m, (1 + x l ^ 2) ^ (-1 : ℝ) with hD
  have hDi : Integrable D :=
    (integrable_prod_one_add_sq_rpow (fun _ => by norm_num)).const_mul C
  have habsdet : ∀ k : unitaryCompact ℝ m,
      |(((k : Langlands.GeneralLinear m ℝ)⁻¹ : Langlands.GeneralLinear m ℝ) :
        Matrix (Fin m) (Fin m) ℝ).det| = 1 :=
    fun k => abs_det_unitary ⟨_, inv_mem k.2⟩
  set G : unitaryCompact ℝ m × (Fin m → ℝ) → ℂ :=
    fun p => F (iotaGL (p.1 : Langlands.GeneralLinear m ℝ) * chartGL p.2) with hG
  have hGc : Continuous G := hFs.continuous.comp
    ((continuous_iotaGL.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_chartGL.comp continuous_snd))
  have hGb : ∀ (k : unitaryCompact ℝ m) (v : Fin m → ℝ), ‖G (k, v)‖ ≤
      D (v ᵥ* (((k : Langlands.GeneralLinear m ℝ)⁻¹ : Langlands.GeneralLinear m ℝ) :
        Matrix (Fin m) (Fin m) ℝ)) := by
    intro k v
    simp only [hG]
    rw [iotaGL_mul_chartGL]
    exact norm_le_of_covariant hF hC _ (iotaGL_mem_unitaryCompact k.2)
  have hGki : ∀ k : unitaryCompact ℝ m, Integrable fun v => G (k, v) := fun k =>
    Integrable.mono' (integrable_comp_vecMul (det_inv_ne_zero _) hDi)
      (hGc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      (ae_of_all _ (hGb k))
  have hGi : Integrable G ((haarK m).prod volume) := by
    rw [integrable_prod_iff hGc.aestronglyMeasurable]
    refine ⟨ae_of_all _ hGki, ?_⟩
    refine Integrable.of_bound hGc.norm.aestronglyMeasurable.integral_prod_right' (∫ x, D x)
      (ae_of_all _ fun k => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ v, ‖G (k, v)‖ ≤ ∫ v, D (v ᵥ* (((k : Langlands.GeneralLinear m ℝ)⁻¹ :
          Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ)) :=
          integral_mono (hGki k).norm (integrable_comp_vecMul (det_inv_ne_zero _) hDi) (hGb k)
      _ = ∫ x, D x := by
          rw [integral_vecMul_smul (det_inv_ne_zero _), habsdet, inv_one, one_smul]
  calc ∫ v : Fin m → ℝ, natural F (chartGL v)
      = ∫ v : Fin m → ℝ, ∫ k : unitaryCompact ℝ m, G (k, v) ∂haarK m := rfl
    _ = ∫ k : unitaryCompact ℝ m, (∫ v : Fin m → ℝ, G (k, v)) ∂haarK m :=
        (integral_integral_swap (f := fun k v => G (k, v)) hGi).symm
    _ = ∫ k : unitaryCompact ℝ m, (∫ x : Fin m → ℝ,
          F (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℝ))) ∂haarK m := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only [hG]
        simp_rw [iotaGL_mul_chartGL]
        rw [integral_vecMul_eq (det_inv_ne_zero _)
          (fun y => F (chartGL y * iotaGL (k : Langlands.GeneralLinear m ℝ))), habsdet, inv_one,
          Complex.ofReal_one, one_mul]

/-! ## The limit -/

theorem chartGL_zero : chartGL (0 : Fin m → ℝ) = 1 := by
  apply Units.ext
  rw [chartGL, JGL_val, Units.val_one]
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Jmat, Matrix.one_apply]
  all_goals exact fun h => Fin.castSucc_ne_last _ h.symm

theorem iotaGL_mul_dlastGL (k : Langlands.GeneralLinear m ℝ) (s : ℝˣ) :
    iotaGL k * dlastGL s = dlastGL s * iotaGL k := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, iotaGL_val, dlastGL_val]
  exact iota_mul_dlast _ _

theorem apply_dlastGL_mul {χ' : ℕ → ℝˣ → ℂ} {u : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hu : u ∈ principalSeries ℝ (m + 1) χ') (s : ℝˣ) (y : Langlands.GeneralLinear (m + 1) ℝ) :
    u (dlastGL s * y) =
      principalSeriesCharacter ℝ (m + 1) χ' (fun i => Fin.lastCases s (fun _ => 1) i) * u y := by
  have := hu.2 (fun i => Fin.lastCases s (fun _ => 1) i) 1 y
  simpa [dlastGL] using this

/-- **The limit argument.** Let `u` lie in the principal series of `χ⁻¹` and `h` in that of
`χ` on `GL_{m+1}(ℝ)`, with `χ` strictly dominant. If `∫_{O(m+1)} u(κ g) h(κ) dκ = 0` for every
`g`, then `∫_{O(m)} u(ι(k)) (T h)(k) dk = 0`, where `T` is the partial Jacquet integral. -/
theorem integral_mul_jacquetStep_eq_zero (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    {u h : Langlands.GeneralLinear (m + 1) ℝ → ℂ}
    (hu : u ∈ principalSeries ℝ (m + 1) (dualChar χ)) (hh : h ∈ principalSeries ℝ (m + 1) χ)
    (h0 : ∀ g : Langlands.GeneralLinear (m + 1) ℝ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (m + 1) ℝ) * g) * h κ ∂haarK (m + 1) = 0) :
    ∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℝ)) * jacquetStep h k ∂haarK m = 0 := by
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
  obtain ⟨Ch, hCh⟩ := exists_bound_unitaryCompact hh.1.continuous
  have hCu0 : 0 ≤ Cu := le_trans (norm_nonneg _) (hCu 1 (unitaryCompact ℝ (m + 1)).one_mem)
  have hCh0 : 0 ≤ Ch := le_trans (norm_nonneg _) (hCh 1 (unitaryCompact ℝ (m + 1)).one_mem)
  set γ : Fin m → ℝ := fun l => max (chartExponent e l) (-1) with hγdef
  have hγ : ∀ l, γ l < -1 / 2 := fun l => max_lt (chartExponent_lt he l) (by norm_num)
  set D : (Fin m → ℝ) → ℝ := fun x => Cu * Ch * ∏ l : Fin m, (1 + x l ^ 2) ^ γ l with hDdef
  have hDi : Integrable D := (integrable_prod_one_add_sq_rpow hγ).const_mul _
  have hbound : ∀ s : ℝ, 1 ≤ s → ∀ (k : unitaryCompact ℝ m) (x : Fin m → ℝ),
      ‖Φ s (k, x)‖ ≤ D x := by
    intro s hs k x
    simp only [hΦ, hDdef]
    rw [norm_mul]
    have hk := iotaGL_mem_unitaryCompact k.2
    have h1 := norm_le_partialSq hχ.dual hu hCu (s⁻¹ • x) hk
    have h2 := norm_le_partialSq hχ hh hCh x hk
    have hsum : ∀ l : Fin m, chartExponent (fun l => -e l) l + chartExponent e l = -1 := by
      intro l
      unfold chartExponent
      simp only [Complex.neg_re]
      ring
    have hneg : ∀ l : Fin m, chartExponent e l < 0 := fun l => by
      linarith [chartExponent_lt he l]
    have habs : |s⁻¹| ≤ 1 := by
      rw [abs_inv, abs_of_pos (by linarith)]
      exact inv_le_one_of_one_le₀ hs
    have hd := prod_rpow_mul_prod_rpow_le (x := x) habs hsum hneg
    have hp1 : 0 ≤ ∏ l : Fin m, partialSq (s⁻¹ • x) ((l : ℕ) + 1) ^
        chartExponent (fun l => -e l) l :=
      Finset.prod_nonneg fun l _ => (Real.rpow_pos_of_pos (partialSq_pos _ _) _).le
    calc ‖u (chartGL (s⁻¹ • x) * iotaGL (k : Langlands.GeneralLinear m ℝ))‖ *
          ‖h (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℝ))‖
        ≤ (Cu * ∏ l : Fin m, partialSq (s⁻¹ • x) ((l : ℕ) + 1) ^
            chartExponent (fun l => -e l) l) *
          (Ch * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCu0 hp1)
      _ = Cu * Ch * ((∏ l : Fin m, partialSq (s⁻¹ • x) ((l : ℕ) + 1) ^
            chartExponent (fun l => -e l) l) *
          ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l) := by ring
      _ ≤ Cu * Ch * ∏ l : Fin m, (1 + x l ^ 2) ^ γ l :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hCu0 hCh0)
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
  exact (tendsto_nhds_unique hlim tendsto_const_nhds)

end JacquetLimit

end Langlands.Archimedean

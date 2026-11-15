import Langlands.Representation.Archimedean.ComplexPartialJacquet

/-!
# The limit argument along the maximal parabolic subgroup `P_{m,1}` of `GL_{m+1}(ℂ)`

Let `u` lie in the principal series of `χ⁻¹` and `h` in that of a strictly dominant `χ` on
`GL_{m+1}(ℂ)`. If `∫_{U(m+1)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{U(m)} u(ι(k)) T h(k) dk = 0`, where `T` is the partial Jacquet integral
(`ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero`).
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexJacquetLimit

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexPartialJacquet
  ComplexGramFormula Langlands.GeneralLinear ComplexDuality ComplexKIntegralInvariance

variable {m : ℕ}

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- Products of smooth functions on `GL_n(ℂ)` are smooth. -/
theorem contMDiff_mul_fun {n : ℕ} {f h : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f)
    (hh : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ h) :
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ fun g => f g * h g :=
  contMDiff_of_contDiffOn ((contDiffOn_unitsExtension hf).mul (contDiffOn_unitsExtension hh))
    fun g => by rw [unitsExtension_val, unitsExtension_val]

/-- The modulus characters `(|z|²)^{(n-1)/2 - l}` are phase powers. -/
theorem isPhasePower_modulus (n : ℕ) :
    IsPhasePower (modulusCharacter n) (fun l => ((n : ℂ) - 1) / 2 - (l : ℂ)) where
  eq l z := by simp [modulusCharacter, norm_phaseUnit]
  one l := by simp [modulusCharacter]
  norm_phase l z := by simp [modulusCharacter, norm_phaseUnit]

theorem principalSeriesCharacter_dual_mul (hχ : IsPhasePower χ e) (N : ℕ) (a : Fin N → ℂˣ) :
    principalSeriesCharacter ℂ N (dualChar χ) a * principalSeriesCharacter ℂ N χ a =
      principalSeriesCharacter ℂ N (modulusCharacter N) a := by
  unfold principalSeriesCharacter
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [dualChar, modulusCharacter, Complex.finrank_real_complex]
  have hc := hχ.ne_zero i (a i)
  set P := ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))
  rw [show (χ i (a i))⁻¹ * P * (χ i (a i) * P) = ((χ i (a i))⁻¹ * χ i (a i)) * (P * P) by ring,
    inv_mul_cancel₀ hc, one_mul]

/-- The chart bound for a function of the principal series of the modulus character. -/
theorem norm_le_of_modulus {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1))) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℂ (m + 1), ‖F k‖ ≤ C) (x : Fin m → ℂ)
    {κ : Langlands.GeneralLinear (m + 1) ℂ} (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    ‖F (chartGL x * κ)‖ ≤ C * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ (-2 : ℝ) := by
  have hb := norm_le_partialSq (isPhasePower_modulus (m + 1)) hF hC x hκ
  have hexp : ∀ l : Fin m,
      chartExponent (fun l : ℕ => (((m + 1 : ℕ) : ℂ) - 1) / 2 - (l : ℂ)) l = -2 := by
    intro l
    simp only [chartExponent, Complex.sub_re, Complex.natCast_re]
    push_cast
    ring
  simp only [hexp] at hb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℂ (m + 1)).one_mem)
  exact hb.trans (mul_le_mul_of_nonneg_left (prod_partialSq_rpow_le fun _ => by norm_num) hC0)

theorem iotaGL_mul_chartGL (k : Langlands.GeneralLinear m ℂ) (v : Fin m → ℂ) :
    iotaGL k * chartGL v =
      chartGL (v ᵥ* ((k⁻¹ : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ)) *
        iotaGL k := by
  rw [chartGL_mul_iotaGL, vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    vecMul_one]

theorem det_inv_ne_zero (k : Langlands.GeneralLinear m ℂ) :
    ((k⁻¹ : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero

theorem norm_det_inv_sq (k : unitaryCompact ℂ m) :
    ‖(((k : Langlands.GeneralLinear m ℂ)⁻¹ : Langlands.GeneralLinear m ℂ) :
      Matrix (Fin m) (Fin m) ℂ).det‖ ^ 2 = 1 := by
  have h := normSqC_det_unitary (⟨_, inv_mem k.2⟩ : unitaryCompact ℂ m)
  unfold normSqC at h
  exact_mod_cast h

/-- **The integration formula, compact variable outside.**
`∫_{U(m+1)} F = c_m ∫_{U(m)} ∫_{ℂ^m} F(J(x,1) ι(k)) dx dk`. -/
theorem integral_eq_chart' {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1))) :
    ∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1) =
      (chartConstant m : ℂ) * ∫ k : unitaryCompact ℂ m,
        (∫ x : Fin m → ℂ, F (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℂ)))
          ∂unitaryHaar m := by
  rw [integral_eq_chart hF]
  congr 1
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hF.1.continuous
  set D : (Fin m → ℂ) → ℝ := fun x => C * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ (-2 : ℝ) with hD
  have hDi : Integrable D :=
    (integrable_prod_one_add_sq_rpow (fun _ => by norm_num)).const_mul C
  set G : unitaryCompact ℂ m × (Fin m → ℂ) → ℂ :=
    fun p => F (iotaGL (p.1 : Langlands.GeneralLinear m ℂ) * chartGL p.2) with hG
  have hGc : Continuous G := hF.1.continuous.comp
    ((continuous_iotaGL.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_chartGL.comp continuous_snd))
  have hGb : ∀ (k : unitaryCompact ℂ m) (v : Fin m → ℂ), ‖G (k, v)‖ ≤
      D (v ᵥ* (((k : Langlands.GeneralLinear m ℂ)⁻¹ : Langlands.GeneralLinear m ℂ) :
        Matrix (Fin m) (Fin m) ℂ)) := by
    intro k v
    simp only [hG]
    rw [iotaGL_mul_chartGL]
    exact norm_le_of_modulus hF hC _ (iotaGL_mem_unitaryCompact k.2)
  have hGki : ∀ k : unitaryCompact ℂ m, Integrable fun v => G (k, v) := fun k =>
    Integrable.mono' (integrable_comp_vecMul (det_inv_ne_zero _) hDi)
      (hGc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      (ae_of_all _ (hGb k))
  have hGi : Integrable G ((unitaryHaar m).prod volume) := by
    rw [integrable_prod_iff hGc.aestronglyMeasurable]
    refine ⟨ae_of_all _ hGki, ?_⟩
    refine Integrable.of_bound hGc.norm.aestronglyMeasurable.integral_prod_right' (∫ x, D x)
      (ae_of_all _ fun k => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ v, ‖G (k, v)‖ ≤ ∫ v, D (v ᵥ* (((k : Langlands.GeneralLinear m ℂ)⁻¹ :
          Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ)) :=
          integral_mono (hGki k).norm (integrable_comp_vecMul (det_inv_ne_zero _) hDi) (hGb k)
      _ = ∫ x, D x := by
          rw [integral_vecMul_smul (det_inv_ne_zero _), norm_det_inv_sq, inv_one, one_smul]
  calc ∫ v : Fin m → ℂ, natural F (chartGL v)
      = ∫ v : Fin m → ℂ, ∫ k : unitaryCompact ℂ m, G (k, v) ∂unitaryHaar m := rfl
    _ = ∫ k : unitaryCompact ℂ m, (∫ v : Fin m → ℂ, G (k, v)) ∂unitaryHaar m :=
        (integral_integral_swap (f := fun k v => G (k, v)) hGi).symm
    _ = ∫ k : unitaryCompact ℂ m, (∫ x : Fin m → ℂ,
          F (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℂ))) ∂unitaryHaar m := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only [hG]
        simp_rw [iotaGL_mul_chartGL]
        rw [integral_vecMul_eq (det_inv_ne_zero _)
          (fun y => F (chartGL y * iotaGL (k : Langlands.GeneralLinear m ℂ))), norm_det_inv_sq,
          inv_one, Complex.ofReal_one, one_mul]

/-! ## The limit -/

theorem chartGL_zero : chartGL (0 : Fin m → ℂ) = 1 := by
  apply Units.ext
  rw [chartGL, JGL_val, Units.val_one]
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Jmat, Matrix.one_apply]
  all_goals exact fun h => Fin.castSucc_ne_last _ h.symm

theorem iotaGL_mul_dlastGL (k : Langlands.GeneralLinear m ℂ) (s : ℂˣ) :
    iotaGL k * dlastGL s = dlastGL s * iotaGL k := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, iotaGL_val, dlastGL_val]
  exact iota_mul_dlast _ _

theorem apply_dlastGL_mul {χ' : ℕ → ℂˣ → ℂ} {u : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (m + 1) χ') (s : ℂˣ) (y : Langlands.GeneralLinear (m + 1) ℂ) :
    u (dlastGL s * y) =
      principalSeriesCharacter ℂ (m + 1) χ' (fun i => Fin.lastCases s (fun _ => 1) i) * u y := by
  have := hu.2 (fun i => Fin.lastCases s (fun _ => 1) i) 1 y
  simpa [dlastGL] using this

/-- **The limit argument.** Let `u` lie in the principal series of `χ⁻¹` and `h` in that of
`χ` on `GL_{m+1}(ℂ)`, with `χ` strictly dominant. If `∫_{U(m+1)} u(κ g) h(κ) dκ = 0` for every
`g`, then `∫_{U(m)} u(ι(k)) (T h)(k) dk = 0`, where `T` is the partial Jacquet integral. -/
theorem integral_mul_jacquetStep_eq_zero (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    {u h : Langlands.GeneralLinear (m + 1) ℂ → ℂ}
    (hu : u ∈ principalSeries ℂ (m + 1) (dualChar χ)) (hh : h ∈ principalSeries ℂ (m + 1) χ)
    (h0 : ∀ g : Langlands.GeneralLinear (m + 1) ℂ,
      ∫ κ, u ((κ : Langlands.GeneralLinear (m + 1) ℂ) * g) * h κ ∂unitaryHaar (m + 1) = 0) :
    ∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep h k ∂unitaryHaar m = 0 := by
  set Φ : ℝ → unitaryCompact ℂ m × (Fin m → ℂ) → ℂ := fun s p =>
    u (chartGL (((s : ℂ))⁻¹ • p.2) * iotaGL (p.1 : Langlands.GeneralLinear m ℂ)) *
      h (chartGL p.2 * iotaGL (p.1 : Langlands.GeneralLinear m ℂ)) with hΦ
  have hΦc : ∀ s, Continuous (Φ s) := by
    intro s
    have hk : Continuous fun p : unitaryCompact ℂ m × (Fin m → ℂ) =>
        iotaGL (p.1 : Langlands.GeneralLinear m ℂ) :=
      continuous_iotaGL.comp (continuous_subtype_val.comp continuous_fst)
    have h1 : Continuous fun p : unitaryCompact ℂ m × (Fin m → ℂ) =>
        chartGL (((s : ℂ))⁻¹ • p.2) :=
      continuous_chartGL.comp (continuous_snd.const_smul ((s : ℂ))⁻¹)
    have h2 : Continuous fun p : unitaryCompact ℂ m × (Fin m → ℂ) => chartGL p.2 :=
      continuous_chartGL.comp continuous_snd
    simp only [hΦ]
    exact (hu.1.continuous.comp (h1.mul hk)).mul (hh.1.continuous.comp (h2.mul hk))
  -- the pairing identity
  have hI : ∀ s : ℝ, 0 < s → ∫ k : unitaryCompact ℂ m, (∫ x, Φ s (k, x)) ∂unitaryHaar m = 0 := by
    intro s hs
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    set s' : ℂˣ := Units.mk0 (s : ℂ) hs0 with hs'
    have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu (dlastGL s')
    set F : Langlands.GeneralLinear (m + 1) ℂ → ℂ :=
      fun y => u (y * dlastGL s') * h y with hFdef
    have hF : F ∈ principalSeries ℂ (m + 1) (modulusCharacter (m + 1)) := by
      refine ⟨contMDiff_mul_fun hud.1 hh.1, fun a v y => ?_⟩
      simp only [hFdef]
      rw [mul_assoc _ y, hu.2 a v, hh.2 a v y, ← principalSeriesCharacter_dual_mul hχ]
      ring
    have h1 := integral_eq_chart' hF
    rw [show (∫ κ, F (κ : Langlands.GeneralLinear (m + 1) ℂ) ∂unitaryHaar (m + 1)) = 0 from
      h0 _] at h1
    set c' := principalSeriesCharacter ℂ (m + 1) (dualChar χ)
      (fun i => Fin.lastCases s' (fun _ => 1) i) with hc'def
    have hpt : ∀ (k : unitaryCompact ℂ m) (x : Fin m → ℂ),
        F (chartGL x * iotaGL (k : Langlands.GeneralLinear m ℂ)) = c' * Φ s (k, x) := by
      intro k x
      simp only [hFdef, hΦ]
      rw [mul_assoc, iotaGL_mul_dlastGL, ← mul_assoc, chartGL_mul_dlastGL, mul_assoc,
        apply_dlastGL_mul hu, hs', Units.val_mk0]
      ring
    simp_rw [hpt, integral_const_mul] at h1
    have hc : (chartConstant m : ℂ) ≠ 0 := by exact_mod_cast (chartConstant_pos m).ne'
    have hc' : c' ≠ 0 := by
      rw [← norm_ne_zero_iff, hc'def, norm_principalSeriesCharacter hχ.dual]
      exact (Finset.prod_pos fun l _ =>
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (Units.ne_zero _)) _).ne'
    have h2 := h1.symm
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hc
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hc'
      · exact h4
  -- the domination
  obtain ⟨Cu, hCu⟩ := exists_bound_unitaryCompact hu.1.continuous
  obtain ⟨Ch, hCh⟩ := exists_bound_unitaryCompact hh.1.continuous
  have hCu0 : 0 ≤ Cu := le_trans (norm_nonneg _) (hCu 1 (unitaryCompact ℂ (m + 1)).one_mem)
  have hCh0 : 0 ≤ Ch := le_trans (norm_nonneg _) (hCh 1 (unitaryCompact ℂ (m + 1)).one_mem)
  set γ : Fin m → ℝ := fun l => max (chartExponent e l) (-2) with hγdef
  have hγ : ∀ l, γ l < -1 := fun l => max_lt (chartExponent_lt he l) (by norm_num)
  set D : (Fin m → ℂ) → ℝ := fun x => Cu * Ch * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ γ l with hDdef
  have hDi : Integrable D := (integrable_prod_one_add_sq_rpow hγ).const_mul _
  have hbound : ∀ s : ℝ, 1 ≤ s → ∀ (k : unitaryCompact ℂ m) (x : Fin m → ℂ),
      ‖Φ s (k, x)‖ ≤ D x := by
    intro s hs k x
    simp only [hΦ, hDdef]
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
  -- the limit
  have hlim : Tendsto (fun n : ℕ => ∫ k : unitaryCompact ℂ m,
      (∫ x, Φ ((n : ℝ) + 1) (k, x)) ∂unitaryHaar m) atTop
      (𝓝 (∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℂ)) * jacquetStep h k
        ∂unitaryHaar m)) := by
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
  have hzero : ∀ n : ℕ,
      ∫ k : unitaryCompact ℂ m, (∫ x, Φ ((n : ℝ) + 1) (k, x)) ∂unitaryHaar m = 0 :=
    fun n => hI _ (by linarith [hn1 n])
  simp only [hzero] at hlim
  exact (tendsto_nhds_unique hlim tendsto_const_nhds)

end ComplexJacquetLimit

open ComplexDuality in
/-- **The limit argument along `P_{m,1}` of `GL_{m+1}(ℂ)`.** Let `χ_0, …, χ_m` be characters
of `ℂˣ` with `χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, `|χ_l| = 1` on the unit circle and
`Re e_0 > ⋯ > Re e_m`. Let `u` lie in the smooth principal series of the inverse characters and
`h` in that of `χ` on `GL_{m+1}(ℂ)`. If `∫_{U(m+1)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{U(m)} u(diag(k,1)) (∫_{ℂ^m} h(J(x,1) diag(k,1)) dx) dk = 0`, where `J(x,1)` is the identity
matrix with last row `(x, 1)` and `dk`, `dκ` are the Haar probability measures. -/
def ComplexJacquetLimitStatement : Prop :=
  ∀ (m : ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), ‖χ l (ComplexGramFormula.phaseUnit z)‖ = 1) →
    (∀ l : ℕ, l < m → (e (l + 1)).re < (e l).re) →
    ∀ u ∈ principalSeries ℂ (m + 1) (fun l z => (χ l z)⁻¹),
    ∀ h ∈ principalSeries ℂ (m + 1) χ,
      (∀ g : Langlands.GeneralLinear (m + 1) ℂ,
        ∫ κ, u ((κ : Langlands.GeneralLinear (m + 1) ℂ) * g) * h κ ∂unitaryHaar (m + 1) = 0) →
      ∫ k, u (ComplexMaximalParabolicIntegration.iotaGL (k : Langlands.GeneralLinear m ℂ)) *
          (∫ x : Fin m → ℂ, h (ComplexMaximalParabolicIntegration.chartGL x *
            ComplexMaximalParabolicIntegration.iotaGL (k : Langlands.GeneralLinear m ℂ)))
        ∂unitaryHaar m = 0

theorem complexJacquetLimit : ComplexJacquetLimitStatement := by
  intro m χ e heq hone hphase hdom u hu h hh h0
  have hχ : ComplexPartialJacquet.IsPhasePower χ e := ⟨heq, hone, hphase⟩
  exact ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero hχ hdom hu hh h0

end Langlands.Archimedean

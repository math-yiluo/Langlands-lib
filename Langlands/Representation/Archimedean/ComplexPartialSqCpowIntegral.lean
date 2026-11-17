import Langlands.Representation.Archimedean.ComplexPartialSqIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrals of complex powers of partial square sums

For `A > 0` and `Re β < -1`, `∫_ℂ (A + |t|²)^β dt = -π A^{β+1}/(β + 1)` (complex powers of positive
reals; `integral_add_sq_cpow`). Consequently, for `r_l(x) = 1 + ∑_{j<l} |x_j|²`
(`ComplexParabolicChartBound.partialSq`), complex exponents `β_l` with `Re β_l < -1` and `δ` with
`Re δ ≤ 0`, the integral of `r_m(x)^δ ∏_{l<m} r_{l+1}(x)^{β_l}` over `ℂ^m` is nonzero
(`integral_partialSq_cpow_ne_zero`).
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace Langlands.Archimedean

set_option autoImplicit false

namespace ComplexPartialSqCpow

open ComplexParabolicChartBound ComplexPartialSqIntegral

/-! ## One complex variable -/

theorem add_one_ne_zero_of_re {β : ℂ} (hβ : β.re < -1) : β + 1 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
  linarith

theorem ne_neg_one_of_re {β : ℂ} (hβ : β.re < -1) : β ≠ -1 := by
  intro h
  rw [h] at hβ
  simp at hβ

/-- An antiderivative of `r (A + r²)^β`. -/
theorem hasDerivAt_add_sq_cpow {A : ℝ} (hA : 0 < A) {β : ℂ} (hβ : β.re < -1) (r : ℝ) :
    HasDerivAt (fun r : ℝ => ((A + r ^ 2 : ℝ) : ℂ) ^ (β + 1) / (β + 1) / 2)
      ((r : ℂ) * ((A + r ^ 2 : ℝ) : ℂ) ^ β) r := by
  have hpos : (A + r ^ 2) ≠ 0 := by positivity
  have h1 := hasDerivAt_ofReal_cpow_const' hpos (ne_neg_one_of_re hβ)
  have h2 : HasDerivAt (fun r : ℝ => A + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add A
  have h3 := (h1.scomp r h2).div_const 2
  convert h3 using 1
  · rfl
  · rw [Complex.real_smul]
    push_cast
    ring

theorem norm_add_sq_cpow {A : ℝ} (hA : 0 < A) (β : ℂ) (r : ℝ) :
    ‖((A + r ^ 2 : ℝ) : ℂ) ^ β‖ = (A + r ^ 2) ^ β.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) β

theorem tendsto_add_sq_cpow {A : ℝ} (hA : 0 < A) {γ : ℂ} (hγ : γ.re < 0) :
    Tendsto (fun r : ℝ => ((A + r ^ 2 : ℝ) : ℂ) ^ γ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_add_sq_cpow hA]
  have h1 : Tendsto (fun r : ℝ => A + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 := (tendsto_rpow_neg_atTop (y := -γ.re) (by linarith)).comp h1
  simpa [Function.comp_def] using h2

/-- The radial integral `∫_0^∞ r (A + r²)^β dr = -A^{β+1}/(2(β+1))`. -/
theorem integral_Ioi_mul_add_sq_cpow {A : ℝ} (hA : 0 < A) {β : ℂ} (hβ : β.re < -1) :
    ∫ r in Ioi (0 : ℝ), (r : ℂ) * ((A + r ^ 2 : ℝ) : ℂ) ^ β =
      -((A : ℂ) ^ (β + 1)) / (β + 1) / 2 := by
  have hβ1 := add_one_ne_zero_of_re hβ
  have hint : IntegrableOn (fun r : ℝ => (r : ℂ) * ((A + r ^ 2 : ℝ) : ℂ) ^ β) (Ioi 0) := by
    -- the norm is the derivative of a real function with a limit at infinity
    have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt
        (fun r : ℝ => (A + r ^ 2) ^ (β.re + 1) / (β.re + 1) / 2) (r * (A + r ^ 2) ^ β.re) r := by
      intro r _
      have hp : 0 < A + r ^ 2 := by positivity
      have h1 : HasDerivAt (fun r : ℝ => A + r ^ 2) (2 * r) r := by
        simpa using (hasDerivAt_pow 2 r).const_add A
      have h2 := ((h1.rpow_const (p := β.re + 1) (Or.inl hp.ne')).div_const (β.re + 1)).div_const 2
      have hγ : β.re + 1 ≠ 0 := by linarith
      convert h2 using 1
      rw [add_sub_cancel_right]
      field_simp
    have hlim : Tendsto (fun r : ℝ => (A + r ^ 2) ^ (β.re + 1) / (β.re + 1) / 2) atTop
        (𝓝 (0 / (β.re + 1) / 2)) := by
      have h1 : Tendsto (fun r : ℝ => A + r ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
      have h2 := (tendsto_rpow_neg_atTop (y := -(β.re + 1)) (by linarith)).comp h1
      simp only [neg_neg, Function.comp_def] at h2
      exact (h2.div_const _).div_const _
    have hcont : ContinuousWithinAt (fun r : ℝ => (A + r ^ 2) ^ (β.re + 1) / (β.re + 1) / 2)
        (Ici 0) 0 := by
      refine Continuous.continuousWithinAt ?_
      exact (((continuous_const.add (continuous_pow 2)).rpow_const fun r => Or.inl
        (add_pos_of_pos_of_nonneg hA (sq_nonneg r)).ne').div_const _).div_const _
    have hg := integrableOn_Ioi_deriv_of_nonneg hcont hderiv
      (fun r hr => mul_nonneg (le_of_lt hr) (Real.rpow_nonneg (by positivity) _)) hlim
    have hfc : Continuous fun r : ℝ => (r : ℂ) * ((A + r ^ 2 : ℝ) : ℂ) ^ β := by
      refine Complex.continuous_ofReal.mul ?_
      refine (Complex.continuous_ofReal.comp (continuous_const.add (continuous_pow 2))).cpow
        continuous_const fun r => ?_
      exact Complex.ofReal_mem_slitPlane.mpr (add_pos_of_pos_of_nonneg hA (sq_nonneg r))
    refine Integrable.mono' hg hfc.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    rw [norm_mul, Complex.norm_real, norm_add_sq_cpow hA, Real.norm_of_nonneg (le_of_lt hr)]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_add_sq_cpow hA hβ 0).continuousAt.continuousWithinAt
    (fun r _ => hasDerivAt_add_sq_cpow hA hβ r) hint
    (((tendsto_add_sq_cpow hA (γ := β + 1) (by simp; linarith)).div_const (β + 1)).div_const 2)
  rw [h]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_div,
    zero_sub]
  ring

/-- `∫_ℂ (A + |t|²)^β dt = -π A^{β+1}/(β+1)` for `A > 0` and `Re β < -1`, by polar
coordinates. -/
theorem integral_add_sq_cpow {A : ℝ} (hA : 0 < A) {β : ℂ} (hβ : β.re < -1) :
    ∫ t : ℂ, ((A + ‖t‖ ^ 2 : ℝ) : ℂ) ^ β = -((Real.pi : ℂ) * (A : ℂ) ^ (β + 1) / (β + 1)) := by
  rw [← Complex.integral_comp_polarCoord_symm]
  have hcongr : EqOn
      (fun p : ℝ × ℝ => p.1 • ((A + ‖Complex.polarCoord.symm p‖ ^ 2 : ℝ) : ℂ) ^ β)
      (fun p : ℝ × ℝ => ((p.1 : ℂ) * ((A + p.1 ^ 2 : ℝ) : ℂ) ^ β) * (1 : ℂ)) polarCoord.target := by
    intro p hp
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    simp only
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1, Complex.real_smul, mul_one]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr, polarCoord_target,
    Measure.volume_eq_prod, setIntegral_prod_mul
      (fun r : ℝ => (r : ℂ) * ((A + r ^ 2 : ℝ) : ℂ) ^ β) (fun _ : ℝ => (1 : ℂ)),
    integral_Ioi_mul_add_sq_cpow hA hβ]
  have hθ : ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    simp only [sub_neg_eq_add, Complex.real_smul, mul_one]
    push_cast
    ring
  rw [hθ]
  have hβ1 := add_one_ne_zero_of_re hβ
  field_simp

/-! ## Several variables -/

theorem continuous_partialSq_cpow {m : ℕ} (l : ℕ) (c : ℂ) :
    Continuous fun y : Fin m → ℂ => ((partialSq y l : ℝ) : ℂ) ^ c :=
  (Complex.continuous_ofReal.comp (continuous_partialSq l)).cpow continuous_const fun y =>
    Complex.ofReal_mem_slitPlane.mpr (partialSq_pos y l)

theorem norm_partialSq_cpow {m : ℕ} (y : Fin m → ℂ) (l : ℕ) (c : ℂ) :
    ‖((partialSq y l : ℝ) : ℂ) ^ c‖ = partialSq y l ^ c.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (partialSq_pos y l) c

/-- The integrand `r_m(y)^δ ∏_{l<m} r_{l+1}(y)^{β_l}`. -/
def integrand (m : ℕ) (β : Fin m → ℂ) (δ : ℂ) (y : Fin m → ℂ) : ℂ :=
  ((partialSq y m : ℝ) : ℂ) ^ δ * ∏ l : Fin m, ((partialSq y ((l : ℕ) + 1) : ℝ) : ℂ) ^ β l

theorem continuous_integrand (m : ℕ) (β : Fin m → ℂ) (δ : ℂ) :
    Continuous (integrand m β δ) :=
  (continuous_partialSq_cpow m δ).mul
    (continuous_finsetProd _ fun _ _ => continuous_partialSq_cpow _ _)

theorem integrable_integrand (m : ℕ) (β : Fin m → ℂ) (δ : ℂ) (hβ : ∀ l, (β l).re < -1)
    (hδ : δ.re ≤ 0) : Integrable (integrand m β δ) := by
  have htail : TailCondition (fun l => (β l).re) δ.re := by
    intro j
    have hle : ∑ l : Fin m, (if j ≤ l then (β l).re + 1 else 0) ≤ (β j).re + 1 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      simp only [le_refl, ite_true]
      have : ∑ l ∈ Finset.univ.erase j, (if j ≤ l then (β l).re + 1 else 0) ≤ 0 :=
        Finset.sum_nonpos fun l _ => by
          split_ifs
          · linarith [hβ l]
          · exact le_rfl
      linarith
    linarith [hβ j]
  have h := integrable_partialSq_mul_prod m (fun l => (β l).re) δ.re htail
  refine h.mono' (continuous_integrand m β δ).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [integrand, norm_mul, norm_partialSq_cpow, norm_prod]
  simp only [norm_partialSq_cpow]
  exact le_rfl

/-- **Nonvanishing.** For `Re β_l < -1` and `Re δ ≤ 0`,
`∫_{ℂ^m} r_m(y)^δ ∏_{l<m} r_{l+1}(y)^{β_l} dy ≠ 0`. -/
theorem integral_integrand_ne_zero : ∀ (m : ℕ) (β : Fin m → ℂ) (δ : ℂ),
    (∀ l, (β l).re < -1) → δ.re ≤ 0 → ∫ y, integrand m β δ y ≠ 0
  | 0, β, δ, _, _ => by
      have h1 : integrand 0 β δ = fun _ => 1 := by
        funext y
        simp [integrand, partialSq_zero]
      rw [h1, integral_const]
      simp [Measure.real, volume_pi]
  | m + 1, β, δ, hβ, hδ => by
      set β' : ℂ := δ + β (Fin.last m) with hβ'def
      have hβ' : β'.re < -1 := by
        simp only [hβ'def, Complex.add_re]
        linarith [hβ (Fin.last m)]
      set γ : Fin m → ℂ := fun l => β (Fin.castSucc l) with hγdef
      have hIH := integral_integrand_ne_zero m γ (β' + 1) (fun l => hβ _) (by
        simp only [Complex.add_re, Complex.one_re]
        linarith)
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)
      have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)
      set G : ℂ × (Fin m → ℂ) → ℂ := fun p =>
        ((partialSq p.2 m + ‖p.1‖ ^ 2 : ℝ) : ℂ) ^ β' * integrand m γ 0 p.2 with hGdef
      have key : ∀ p, integrand (m + 1) β δ (e.symm p) = G p := by
        rintro ⟨t, y⟩
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, hGdef, integrand]
        have hx : (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℂ) (Fin.last m)) (t, y) =
            (Fin.snoc y t : Fin (m + 1) → ℂ) := Fin.insertNth_last' _ _
        rw [hx, Fin.prod_univ_castSucc]
        simp only [partialSq_snoc_castSucc, Fin.val_castSucc, Fin.val_last]
        rw [partialSq_snoc_last]
        have hpos : ((partialSq y m + ‖t‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
          have := partialSq_pos y m
          exact_mod_cast (by positivity : (0 : ℝ) < partialSq y m + ‖t‖ ^ 2).ne'
        rw [hβ'def, Complex.cpow_add _ _ hpos, Complex.cpow_zero]
        simp only [hγdef]
        ring
      have hGint : Integrable G (volume.prod volume) := by
        have h := integrable_integrand (m + 1) β δ hβ hδ
        rw [← Measure.volume_eq_prod]
        have h2 := (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr h
        refine h2.congr (ae_of_all _ fun p => ?_)
        exact key p
      have hcalc : ∫ y, integrand (m + 1) β δ y =
          (-((Real.pi : ℂ) / (β' + 1))) * ∫ y, integrand m γ (β' + 1) y := by
        calc ∫ y, integrand (m + 1) β δ y
            = ∫ p, integrand (m + 1) β δ (e.symm p) :=
              (hmp.symm.integral_comp e.symm.measurableEmbedding _).symm
          _ = ∫ p, G p := by
              congr 1
              funext p
              exact key p
          _ = ∫ y, ∫ t, G (t, y) := by
              rw [Measure.volume_eq_prod]
              exact integral_prod_symm G hGint
          _ = ∫ y, (-((Real.pi : ℂ) / (β' + 1))) * integrand m γ (β' + 1) y := by
              congr 1
              funext y
              simp only [hGdef]
              rw [integral_mul_const, integral_add_sq_cpow (partialSq_pos y m) hβ', integrand,
                integrand]
              simp only [Complex.cpow_zero, one_mul]
              ring
          _ = _ := integral_const_mul _ _
      rw [hcalc]
      refine mul_ne_zero ?_ hIH
      refine neg_ne_zero.mpr (div_ne_zero ?_ (add_one_ne_zero_of_re hβ'))
      exact_mod_cast Real.pi_ne_zero

end ComplexPartialSqCpow

end Langlands.Archimedean

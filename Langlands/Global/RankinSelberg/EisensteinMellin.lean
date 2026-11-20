import Langlands.Global.RankinSelberg.EisensteinThetaBounds
import Langlands.Global.RankinSelberg.UnequalAnalyticHolomorphy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Convergence and the positive theta Mellin tail -/

noncomputable section
universe u
open NumberField MeasureTheory Set Langlands.Global
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Eisenstein

open EqualAnalytic

local instance mellinSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance mellinSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)

/-- The idele Haar measure restricted to the rational-idele fundamental domain. -/
abbrev ideleQuotientMeasure : Measure (Points F 1) :=
  (ideleMeasure F).restrict (ideleDomain F)

/-- The logarithmic determinant norm of the point along a scalar idele fibre. -/
def mellinHeight (g : Points F (r + 1)) (a : Points F 1) : ℝ :=
  Real.log (detNorm F (r + 1) (zeta F (r + 1) a * g))

theorem mellinHeight_eq (g : Points F (r + 1)) (a : Points F 1) :
    mellinHeight F r g a =
      ((r + 1 : ℕ) : ℝ) * logNorm F a + Real.log (detNorm F (r + 1) g) :=
  log_detNorm_zeta_mul F (r + 1) a g

theorem measurable_mellinHeight (g : Points F (r + 1)) : Measurable (mellinHeight F r g) := by
  rw [show mellinHeight F r g = _ from funext (mellinHeight_eq F r g)]
  exact (measurable_const.mul (measurable_logNorm F)).add_const _

/-- The part of the fibre with determinant norm at least one. -/
def positiveLog (g : Points F (r + 1)) : Set (Points F 1) :=
  {a | 0 ≤ mellinHeight F r g a}

theorem measurableSet_positiveLog (g : Points F (r + 1)) :
    MeasurableSet (positiveLog F r g) :=
  measurableSet_le measurable_const (measurable_mellinHeight F r g)

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) {Φ : RowVector F (r + 1) → ℂ}

private def mellinAmplitude (Φ : RowVector F (r + 1) → ℂ) (g : Points F (r + 1))
    (a : Points F 1) : ℂ :=
  ideleChar F χ a * scalarTheta F (r + 1) Φ g a

/-- The integrand obtained by unfolding the Eisenstein series to the idele class group. -/
def mellinIntegrand (Φ : RowVector F (r + 1) → ℂ) (g : Points F (r + 1)) (s : ℂ)
    (a : Points F 1) : ℂ :=
  mellinAmplitude F r χ Φ g a * Complex.exp (s * (mellinHeight F r g a : ℂ))

theorem mellinIntegrand_eq (g : Points F (r + 1)) (s : ℂ) (a : Points F 1) :
    mellinIntegrand F r χ Φ g s a =
      ideleChar F χ a * scalarTheta F (r + 1) Φ g a *
        Complex.exp (s * (mellinHeight F r g a : ℂ)) := rfl

/-- The theta Mellin integral over the fibre of determinant norm at least one. -/
def positiveTail (Φ : RowVector F (r + 1) → ℂ) (g : Points F (r + 1)) (s : ℂ) : ℂ :=
  ∫ a in positiveLog F r g, mellinIntegrand F r χ Φ g s a ∂ideleQuotientMeasure F

private theorem measurable_mellinAmplitude (hΦc : Continuous Φ) (g : Points F (r + 1)) :
    Measurable (mellinAmplitude F r χ Φ g) :=
  (continuous_ideleChar F χ).measurable.mul
    ((stronglyMeasurable_thetaSum F (r + 1) hΦc).measurable.comp
      ((continuous_zeta F (r + 1)).mul continuous_const).measurable)

private def mellinMajorant (Φ : RowVector F (r + 1) → ℂ) (g : Points F (r + 1)) (σ : ℝ)
    (a : Points F 1) : ℝ≥0∞ :=
  ‖ideleChar F χ a‖ₑ * scalarThetaNorm F (r + 1) Φ g a *
    ENNReal.ofReal (Real.exp (σ * mellinHeight F r g a))

private theorem enorm_mellinMoment_le (g : Points F (r + 1)) (σ : ℝ) (a : Points F 1) :
    ‖‖mellinAmplitude F r χ Φ g a‖ * Real.exp (σ * mellinHeight F r g a)‖ₑ ≤
      mellinMajorant F r χ Φ g σ a := by
  rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
    mellinAmplitude, enorm_mul, mellinMajorant]
  gcongr
  exact enorm_thetaSum_le _ _ _

private theorem enorm_mellinIntegrand_le (g : Points F (r + 1)) (s : ℂ) (a : Points F 1) :
    ‖mellinIntegrand F r χ Φ g s a‖ₑ ≤ mellinMajorant F r χ Φ g s.re a := by
  rw [← ofReal_norm, mellinIntegrand, UnequalAnalytic.norm_mul_cexp,
    ← Real.enorm_eq_ofReal (by positivity)]
  exact enorm_mellinMoment_le F r χ g s.re a

private theorem mellinMajorant_le (g : Points F (r + 1)) (a : Points F 1) (σ : ℝ)
    {β α C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hχ : ‖ideleChar F χ a‖ ≤ C * Real.exp (β * logNorm F a))
    (hθ : scalarThetaNorm F (r + 1) Φ g a ≤
      ENNReal.ofReal (B * Real.exp (α * logNorm F a))) :
    mellinMajorant F r χ Φ g σ a ≤ ENNReal.ofReal
      (C * B * Real.exp (σ * Real.log (detNorm F (r + 1) g)) *
        Real.exp ((β + α + σ * ((r + 1 : ℕ) : ℝ)) * logNorm F a)) := by
  rw [mellinMajorant, ← ofReal_norm (ideleChar F χ a)]
  calc
    _ ≤ ENNReal.ofReal (C * Real.exp (β * logNorm F a)) *
        ENNReal.ofReal (B * Real.exp (α * logNorm F a)) *
        ENNReal.ofReal (Real.exp (σ * mellinHeight F r g a)) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C * Real.exp _),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * Real.exp _ * (B * Real.exp _))]
      congr 1
      rw [mellinHeight_eq, mul_add, Real.exp_add]
      calc
        _ = C * B * Real.exp (σ * Real.log (detNorm F (r + 1) g)) *
            (Real.exp (β * logNorm F a) * Real.exp (α * logNorm F a) *
              Real.exp (σ * (((r + 1 : ℕ) : ℝ) * logNorm F a))) := by ring
        _ = _ := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          ring

private theorem lintegral_le_logNorm_integral {T : Set (Points F 1)} (hT : MeasurableSet T)
    {m : Points F 1 → ℝ≥0∞} {v : ℝ → ℝ} (hv : Measurable v)
    (hvi : Integrable v volume) (hv₀ : ∀ y, 0 ≤ v y)
    (h : ∀ a ∈ T, m a ≤ ENNReal.ofReal (v (logNorm F a))) :
    ∫⁻ a in T, m a ∂ideleQuotientMeasure F ≤ ENNReal.ofReal (∫ y, v y) := by
  rw [← lintegral_indicator hT, ofReal_integral_eq_lintegral_ofReal hvi
    (Filter.Eventually.of_forall hv₀), ← lintegral_logNorm F _ hv.ennreal_ofReal]
  refine lintegral_mono fun a => ?_
  by_cases ha : a ∈ T
  · rw [Set.indicator_of_mem ha]
    exact h a ha
  · simp [Set.indicator_of_notMem ha]

private theorem exists_lintegral_majorant_positive_le (hΦd : IsRowDominated F (r + 1) Φ)
    {K : Set (Points F (r + 1))} (hK : IsCompact K) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ σ ≤ b,
      ∫⁻ a in positiveLog F r g, mellinMajorant F r χ Φ g σ a ∂ideleQuotientMeasure F ≤
        ENNReal.ofReal C := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let d : ℝ := (Module.finrank ℚ F : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hlog : Continuous (fun g : Points F (r + 1) => Real.log (detNorm F (r + 1) g)) :=
    (UnequalAnalytic.continuous_detNorm F (r + 1)).log
      (fun g => (UnequalAnalytic.detNorm_pos F g).ne')
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn hlog.continuousOn
  obtain ⟨β, C, hC, hχ⟩ := exists_ideleChar_bound F χ
  obtain ⟨N, hN⟩ := exists_nat_gt (max (((r + 1) * Module.finrank ℚ F : ℕ) : ℝ) ((β + b * n) * d))
  have hN' : (r + 1) * Module.finrank ℚ F < N :=
    Nat.cast_lt (α := ℝ) |>.mp ((le_max_left _ _).trans_lt hN)
  let k := β + -(N / d) + b * n
  have hk : k < 0 := by
    have hk' := (lt_div_iff₀ hd).mpr ((le_max_right _ _).trans_lt hN)
    dsimp [k]
    linarith
  obtain ⟨B, hB, hθ⟩ := exists_scalarThetaNorm_bound F (r + 1) hΦd hK N hN'
  let f : ℝ → ℝ := fun y => C * B * Real.exp (|b| * L) * Real.exp (k * y)
  let I := Ici (-L / n)
  have hf : Continuous f := by fun_prop
  have hf₀ (y : ℝ) : 0 ≤ f y := by dsimp [f]; positivity
  have hfi : IntegrableOn f I :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hk _)).const_mul _
  let v := I.indicator f
  have hv₀ (y : ℝ) : 0 ≤ v y := Set.indicator_nonneg (fun y _ => hf₀ y) _
  refine ⟨∫ y, v y, integral_nonneg hv₀, fun g hg σ hσ => ?_⟩
  refine lintegral_le_logNorm_integral F (measurableSet_positiveLog F r g)
    (hv := hf.measurable.indicator measurableSet_Ici)
    (hfi.integrable_indicator measurableSet_Ici) hv₀ (fun a ha => ?_)
  have ha' : 0 ≤ mellinHeight F r g a := ha
  have hLg : |Real.log (detNorm F (r + 1) g)| ≤ L := by
    simpa only [Real.norm_eq_abs] using hL g hg
  have hy : logNorm F a ∈ I := by
    change -L / n ≤ logNorm F a
    apply (div_le_iff₀ hn).mpr
    rw [mellinHeight_eq] at ha'
    linarith [le_abs_self (Real.log (detNorm F (r + 1) g))]
  have hbg : b * Real.log (detNorm F (r + 1) g) ≤ |b| * L :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hLg (abs_nonneg b))
  rw [show v (logNorm F a) = f (logNorm F a) from Set.indicator_of_mem hy _]
  calc
    _ ≤ mellinMajorant F r χ Φ g b a := by
      unfold mellinMajorant
      gcongr
    _ ≤ _ := (mellinMajorant_le F r χ g a b hC hB (hχ a) (hθ g hg a)).trans (by
      unfold f
      gcongr)

private theorem integrableOn_mellinMoment (hΦc : Continuous Φ)
    (hΦd : IsRowDominated F (r + 1) Φ) (g : Points F (r + 1)) (σ : ℝ) :
    IntegrableOn (fun a => ‖mellinAmplitude F r χ Φ g a‖ *
      Real.exp (σ * mellinHeight F r g a)) (positiveLog F r g) (ideleQuotientMeasure F) := by
  obtain ⟨C, _, hC⟩ := exists_lintegral_majorant_positive_le F r χ hΦd
    (isCompact_singleton (x := g)) σ
  exact ⟨((measurable_mellinAmplitude F r χ hΦc g).norm.mul
    (Real.measurable_exp.comp (measurable_const.mul (measurable_mellinHeight F r g)))).aestronglyMeasurable,
    ((lintegral_mono fun a => enorm_mellinMoment_le F r χ g σ a).trans
      (hC g rfl σ le_rfl)).trans_lt ENNReal.ofReal_lt_top⟩

theorem positiveTail_integrable (hΦc : Continuous Φ) (hΦd : IsRowDominated F (r + 1) Φ)
    (g : Points F (r + 1)) (s : ℂ) :
    IntegrableOn (mellinIntegrand F r χ Φ g s) (positiveLog F r g) (ideleQuotientMeasure F) :=
  UnequalAnalytic.integrable_mul_cexp (measurable_mellinAmplitude F r χ hΦc g).aestronglyMeasurable
    (measurable_mellinHeight F r g).aestronglyMeasurable (integrableOn_mellinMoment F r χ hΦc hΦd g) s

theorem positiveTail_differentiable (hΦc : Continuous Φ) (hΦd : IsRowDominated F (r + 1) Φ)
    (g : Points F (r + 1)) : Differentiable ℂ (positiveTail F r χ Φ g) :=
  UnequalAnalytic.differentiable_integral_mul_cexp
    (measurable_mellinAmplitude F r χ hΦc g).aestronglyMeasurable
    (measurable_mellinHeight F r g).aestronglyMeasurable (integrableOn_mellinMoment F r χ hΦc hΦd g)

/-- The positive tail is uniformly bounded on a left half-plane for `g` in a compact set. -/
theorem exists_positiveTail_bound (hΦd : IsRowDominated F (r + 1) Φ)
    {K : Set (Points F (r + 1))} (hK : IsCompact K) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ K, ∀ s : ℂ, s.re ≤ b → ‖positiveTail F r χ Φ g s‖ ≤ C := by
  obtain ⟨C, hC₀, hC⟩ := exists_lintegral_majorant_positive_le F r χ hΦd hK b
  refine ⟨C, hC₀, fun g hg s hs => (ENNReal.ofReal_le_ofReal_iff hC₀).mp ?_⟩
  rw [ofReal_norm, positiveTail]
  exact (enorm_integral_le_lintegral_enorm _).trans
    ((lintegral_mono fun a => enorm_mellinIntegrand_le F r χ g s a).trans (hC g hg s.re hs))

private theorem exists_mellinMajorant_lt_top (hΦd : IsRowDominated F (r + 1) Φ) :
    ∃ σ₀ : ℝ, ∀ (g : Points F (r + 1)) (σ : ℝ), σ₀ < σ →
      ∫⁻ a, mellinMajorant F r χ Φ g σ a ∂ideleQuotientMeasure F < ⊤ := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  let N := (r + 1) * Module.finrank ℚ F + 1
  let α : ℝ := -(N / (Module.finrank ℚ F : ℝ))
  obtain ⟨β, C, hC, hχ⟩ := exists_ideleChar_bound F χ
  refine ⟨-(β + α) / n, fun g σ hσ => ?_⟩
  obtain ⟨B, hB, hθ⟩ := exists_scalarThetaNorm_bound F (r + 1) hΦd
    (isCompact_singleton (x := g)) N (Nat.lt_succ_self _)
  let k := β + α + σ * n
  have hk : 0 < k := by
    have h := (div_lt_iff₀ hn).mp hσ
    dsimp [k]
    linarith
  let L := Real.log (detNorm F (r + 1) g)
  let I := Iic (-L / n)
  let f : ℝ → ℝ := fun y => C * B * Real.exp (σ * L) * Real.exp (k * y)
  have hf : Continuous f := by fun_prop
  have hf₀ (y : ℝ) : 0 ≤ f y := by dsimp [f]; positivity
  have hfi : IntegrableOn f I := (integrableOn_exp_mul_Iic hk _).const_mul _
  have hv₀ (y : ℝ) : 0 ≤ I.indicator f y := Set.indicator_nonneg (fun y _ => hf₀ y) _
  have hneg :
      ∫⁻ a in (positiveLog F r g)ᶜ, mellinMajorant F r χ Φ g σ a
          ∂ideleQuotientMeasure F < ⊤ := by
    refine (lintegral_le_logNorm_integral F (measurableSet_positiveLog F r g).compl
      (hf.measurable.indicator measurableSet_Iic) (hfi.integrable_indicator measurableSet_Iic)
      hv₀ (fun a ha => ?_)).trans_lt ENNReal.ofReal_lt_top
    have hheight : mellinHeight F r g a < 0 := lt_of_not_ge ha
    rw [mellinHeight_eq] at hheight
    change n * logNorm F a + L < 0 at hheight
    have hy : logNorm F a ∈ I := by
      change logNorm F a ≤ -L / n
      apply (le_div_iff₀ hn).mpr
      rw [mul_comm (logNorm F a) n]
      linarith only [hheight]
    rw [Set.indicator_of_mem hy]
    exact mellinMajorant_le F r χ g a σ hC hB (hχ a) (hθ g rfl a)
  obtain ⟨D, _, hD⟩ := exists_lintegral_majorant_positive_le F r χ hΦd
    (isCompact_singleton (x := g)) σ
  rw [← lintegral_add_compl _ (measurableSet_positiveLog F r g)]
  exact ENNReal.add_lt_top.mpr ⟨(hD g rfl σ le_rfl).trans_lt ENNReal.ofReal_lt_top, hneg⟩

private theorem mellinMajorant_eq (g : Points F (r + 1)) (s : ℂ) (a : Points F 1) :
    mellinMajorant F r χ Φ g s.re a =
      ‖detPower F (r + 1) g s‖ₑ *
        (‖sectionWeight (F := F) r χ s a‖ₑ * scalarThetaNorm F (r + 1) Φ g a) := by
  have h : ENNReal.ofReal (Real.exp (s.re * mellinHeight F r g a)) =
      ‖detPower F (r + 1) (zeta F (r + 1) a * g) s‖ₑ := by
    rw [← ofReal_norm, UnequalAnalytic.norm_detPower, mellinHeight]
  rw [mellinMajorant, h, detPower_zeta_mul F r, sectionWeight]
  simp only [enorm_mul]
  ring

/-- On one right half-plane, the Eisenstein sections are integrable and the series
converges absolutely to the unfolded theta Mellin integral at every group point. -/
theorem exists_convergence_abscissa (hΦc : Continuous Φ) (hΦd : IsRowDominated F (r + 1) Φ) :
    ∃ σ₀ : ℝ, ∀ (g : Points F (r + 1)) (s : ℂ), σ₀ < s.re →
      Integrable (mellinIntegrand F r χ Φ g s) (ideleQuotientMeasure F) ∧
      Integrable (eisensteinSectionIntegrand F χ Φ s g) (ideleMeasure F) ∧
      Summable (fun q : LeftCosetSpace (eisensteinParabolic F r) =>
        ‖eisensteinSection F χ Φ s (rationalPoint F (r + 1) q.out * g)‖) ∧
      eisensteinSeries F χ Φ s g = ∫ a, mellinIntegrand F r χ Φ g s a ∂ideleQuotientMeasure F := by
  obtain ⟨σ₀, hbound⟩ := exists_mellinMajorant_lt_top F r χ hΦd
  refine ⟨σ₀, fun g s hs => ?_⟩
  have hweighted (x : Points F (r + 1)) :
      ∫⁻ a, ‖sectionWeight (F := F) r χ s a‖ₑ * scalarThetaNorm F (r + 1) Φ x a
        ∂ideleQuotientMeasure F ≠ ⊤ := by
    intro htop
    have hx := hbound x s.re hs
    have hd : ‖detPower F (r + 1) x s‖ₑ ≠ 0 := enorm_ne_zero.2 (Complex.exp_ne_zero _)
    simp only [mellinMajorant_eq] at hx
    rw [lintegral_const_mul' _ _ enorm_ne_top, htop, ENNReal.mul_top hd] at hx
    exact lt_irrefl _ hx
  have hunfold (x : Points F (r + 1)) :
      (∑' q : LeftCosetSpace (eisensteinParabolic F r),
        ∫⁻ a, ‖eisensteinSectionIntegrand F χ Φ s (rationalPoint F (r + 1) q.out * x) a‖ₑ
          ∂ideleMeasure F) ≠ ⊤ := by
    simp only [eisensteinSectionIntegrand_eq, enorm_mul]
    rw [tsum_lintegral_section F r hΦc _ (continuous_sectionWeight F r χ s).measurable.enorm
      (fun f a => by simp only [sectionWeight_ratUnit_mul])]
    exact hweighted x
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨((measurable_mellinAmplitude F r χ hΦc g).mul
      (Complex.continuous_exp.measurable.comp (measurable_const.mul
        (Complex.continuous_ofReal.measurable.comp (measurable_mellinHeight F r g))))).aestronglyMeasurable,
      (lintegral_mono fun a => enorm_mellinIntegrand_le F r χ g s a).trans_lt (hbound g s.re hs)⟩
  · let q : LeftCosetSpace (eisensteinParabolic F r) := LeftCosetSpace.mk _ 1
    let x := (rationalPoint F (r + 1) q.out)⁻¹ * g
    have hx : rationalPoint F (r + 1) q.out * x = g := by simp [x]
    rw [← hx]
    refine ⟨?_, (ENNReal.le_tsum (f := fun q' : LeftCosetSpace (eisensteinParabolic F r) =>
      ∫⁻ a, ‖eisensteinSectionIntegrand F χ Φ s (rationalPoint F (r + 1) q'.out * x) a‖ₑ
        ∂ideleMeasure F) q).trans_lt (lt_top_iff_ne_top.2 (hunfold x))⟩
    rw [show eisensteinSectionIntegrand F χ Φ s (rationalPoint F (r + 1) q.out * x) =
      (fun a => sectionRow F r Φ q.out x a * sectionWeight (F := F) r χ s a) from
        funext (eisensteinSectionIntegrand_eq F r χ Φ s q.out x)]
    exact ((continuous_sectionRow F r hΦc q.out x).mul
      (continuous_sectionWeight F r χ s)).aestronglyMeasurable
  · apply tsum_enorm_ne_top_iff_summable_norm.mp
    have hterm (q : LeftCosetSpace (eisensteinParabolic F r)) :
        ‖eisensteinSection F χ Φ s (rationalPoint F (r + 1) q.out * g)‖ₑ ≤
          ‖detPower F (r + 1) g s‖ₑ *
            ∫⁻ a, ‖eisensteinSectionIntegrand F χ Φ s (rationalPoint F (r + 1) q.out * g) a‖ₑ
              ∂ideleMeasure F := by
      rw [eisensteinSection, enorm_mul, detPower_rationalPoint_mul]
      gcongr
      exact enorm_integral_le_lintegral_enorm _
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top enorm_ne_top (hunfold g)
  · rw [eisensteinSeries_eq F r χ hΦc s g (hweighted g), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change detPower F (r + 1) g s * (sectionWeight (F := F) r χ s a *
        scalarTheta F (r + 1) Φ g a) =
      ideleChar F χ a * scalarTheta F (r + 1) Φ g a *
        detPower F (r + 1) (zeta F (r + 1) a * g) s
    rw [detPower_zeta_mul F r, sectionWeight]
    ring

end Langlands.Global.RankinSelbergGlobal.Eisenstein

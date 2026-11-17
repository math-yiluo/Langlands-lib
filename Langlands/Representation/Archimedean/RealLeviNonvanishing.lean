import Langlands.Representation.Archimedean.RealLeviBump

/-!
# Nonvanishing of the pairing along a standard parabolic subgroup

Let `ds` satisfy the exponent conditions `RealLeviPairing.Admissible` for the standard parabolic
subgroup `Q` with blocks `sz`, let `u` be an `O(N)`-finite vector of the principal series of the
inverse characters and `f` an `O(N)`-finite vector of the standard module of `ds`. If
`∫_{K_M} psi(u, f)(κ, 0) dκ ≠ 0`, then the pairing `Θ(u, ·)` does not vanish on the
`O(N)`-finite vectors of the standard module (`exists_theta_ne_zero`). The proof replaces `f` by
the bump vectors `ω^m f` (`RealLeviBump.exists_bump_standard`), for which
`Θ(u, ω^m f) = ∫_X β(X)^m F(X) dX` with `F(X) = ∫_{K_M} psi(u, f)(κ, X) dκ`, and lets the
powers `β^m` concentrate at `X = 0` (`concentration`).
-/

noncomputable section

open MeasureTheory Matrix Filter Topology Metric

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviNonvanishing

open RealInducedBlockBound RealInducedTorusCore RealLeviChart GramFormula RealLeviTorus
  RealLeviLimit RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound
  RealStrictCharacterLanglandsQuotient RealLeviModes RealLeviPairing RealLeviBump

/-! ## Concentration -/

section Concentration

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]

/-- **Concentration.** Let `β` be continuous with `0 ≤ β ≤ 1`, `β(0) = 1`, and bounded by a
constant `< 1` outside every ball around `0`. If `F` is integrable, continuous at `0`, and
`∫ β^m F = 0` for every `m`, then `F(0) = 0`. -/
theorem concentration {β : E → ℝ} (hβc : Continuous β) (hβ0 : β 0 = 1)
    (hβpos : ∀ X, 0 ≤ β X) (hβ1 : ∀ X, β X ≤ 1)
    (hgap : ∀ δ : ℝ, 0 < δ → ∃ q < 1, ∀ X : E, δ ≤ ‖X‖ → β X ≤ q)
    {F : E → ℂ} (hF : Integrable F μ) (hF0 : ContinuousAt F 0)
    (hzero : ∀ m : ℕ, ∫ X, ((β X : ℝ) : ℂ) ^ m * F X ∂μ = 0) : F 0 = 0 := by
  by_contra ha
  set a := F 0 with hadef
  set φ : E → ℝ := fun X => (starRingEnd ℂ a * F X).re with hφdef
  have hφi : Integrable φ μ := (hF.const_mul _).re
  have hφc : ContinuousAt φ 0 :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hF0)
  have hφ0 : φ 0 = Complex.normSq a := by
    simp only [hφdef, ← hadef, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  have hφ0pos : 0 < φ 0 := by rw [hφ0]; exact Complex.normSq_pos.mpr ha
  -- a ball on which `φ > φ(0)/2`
  obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.mp hφc (φ 0 / 2) (by linarith)
  have hφB : ∀ X : E, ‖X‖ < δ → φ 0 / 2 < φ X := fun X hX => by
    have h1 := hδφ (by rwa [dist_zero_right])
    rw [Real.dist_eq] at h1
    linarith [neg_abs_le (φ X - φ 0)]
  obtain ⟨q, hq1, hq⟩ := hgap δ hδ
  set qp := max q 0 with hqp
  have hqp1 : qp < 1 := max_lt hq1 zero_lt_one
  have hqp0 : 0 ≤ qp := le_max_right _ _
  set q' := (1 + qp) / 2 with hq'
  have hq'0 : 0 < q' := by rw [hq']; linarith
  have hq'q : qp < q' := by rw [hq']; linarith
  have hq'1 : q' < 1 := by rw [hq']; linarith
  -- a smaller ball on which `β > q'`
  obtain ⟨δ', hδ', hδβ⟩ := Metric.continuousAt_iff.mp hβc.continuousAt (1 - q') (by linarith)
  have hβB : ∀ X : E, ‖X‖ < δ' → q' < β X := fun X hX => by
    have h1 := hδβ (by rwa [dist_zero_right])
    rw [Real.dist_eq, hβ0] at h1
    linarith [neg_abs_le (β X - 1)]
  set ρ := min δ δ' with hρ
  have hρ0 : 0 < ρ := lt_min hδ hδ'
  set B := Metric.ball (0 : E) ρ with hB
  have hBpos : 0 < μ.real B := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos μ 0 hρ0).ne'
      (measure_ball_lt_top (μ := μ)).ne
  set r := qp / q' with hr
  have hr0 : 0 ≤ r := div_nonneg hqp0 hq'0.le
  have hr1 : r < 1 := (div_lt_one hq'0).mpr hq'q
  set I := ∫ X, |φ X| ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun X => abs_nonneg _
  set c0 := φ 0 / 2 * μ.real B with hc0
  have hc0pos : 0 < c0 := mul_pos (by linarith) hBpos
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hc0pos (by linarith : (0 : ℝ) < I + 1)) hr1
  have hrI : r ^ m * I < c0 := by
    have h1 : r ^ m * (I + 1) < c0 := by
      rwa [lt_div_iff₀ (by linarith : (0 : ℝ) < I + 1)] at hm
    nlinarith [pow_nonneg hr0 m]
  -- the pointwise lower bound
  set g : E → ℝ := fun X => q' ^ m * (φ 0 / 2 * B.indicator (fun _ => (1 : ℝ)) X -
    r ^ m * |φ X|) with hg
  have hqr : qp = q' * r := by rw [hr]; field_simp
  have hpt : ∀ X, g X ≤ β X ^ m * φ X := by
    intro X
    have hq'm : 0 ≤ q' ^ m := pow_nonneg hq'0.le m
    by_cases hXB : X ∈ B
    · have hX : ‖X‖ < ρ := by rwa [hB, mem_ball_zero_iff] at hXB
      have hφX := hφB X (hX.trans_le (min_le_left _ _))
      have hβX := hβB X (hX.trans_le (min_le_right _ _))
      have h1 : q' ^ m ≤ β X ^ m := pow_le_pow_left₀ hq'0.le hβX.le m
      simp only [hg, Set.indicator_of_mem hXB, mul_one]
      calc q' ^ m * (φ 0 / 2 - r ^ m * |φ X|) ≤ q' ^ m * (φ 0 / 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith [pow_nonneg hr0 m, abs_nonneg (φ X)]) hq'm
        _ ≤ q' ^ m * φ X := mul_le_mul_of_nonneg_left hφX.le hq'm
        _ ≤ β X ^ m * φ X := mul_le_mul_of_nonneg_right h1 (by linarith)
    · simp only [hg, Set.indicator_of_notMem hXB, mul_zero, zero_sub]
      by_cases hXδ : ‖X‖ < δ
      · have hφX := hφB X hXδ
        have : 0 ≤ β X ^ m * φ X := mul_nonneg (pow_nonneg (hβpos X) m) (by linarith)
        have h2 : q' ^ m * -(r ^ m * |φ X|) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq'm
          (neg_nonpos.mpr (mul_nonneg (pow_nonneg hr0 m) (abs_nonneg _)))
        linarith
      · have hβq : β X ≤ qp := (hq X (not_lt.mp hXδ)).trans (le_max_left _ _)
        have h1 : β X ^ m ≤ qp ^ m := pow_le_pow_left₀ (hβpos X) hβq m
        have h2 : -(β X ^ m * |φ X|) ≤ β X ^ m * φ X := by
          rw [← mul_neg]
          exact mul_le_mul_of_nonneg_left (neg_abs_le _) (pow_nonneg (hβpos X) m)
        calc q' ^ m * -(r ^ m * |φ X|) = -(qp ^ m * |φ X|) := by rw [hqr, mul_pow]; ring
          _ ≤ -(β X ^ m * |φ X|) := neg_le_neg (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
          _ ≤ β X ^ m * φ X := h2
  -- integrability
  have hβm : ∀ m : ℕ, Continuous fun X => β X ^ m := fun m => hβc.pow m
  have hβmφ : Integrable (fun X => β X ^ m * φ X) μ := by
    refine Integrable.mono' hφi.norm ((hβm m).aestronglyMeasurable.mul hφi.1)
      (ae_of_all _ fun X => ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hβpos X) m)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (hβpos X) (hβ1 X))
  have hind : Integrable (B.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (measure_ball_lt_top (μ := μ)).ne)
  have hgi : Integrable g μ :=
    ((hind.const_mul (φ 0 / 2)).sub (hφi.abs.const_mul (r ^ m))).const_mul (q' ^ m)
  have hgint : ∫ X, g X ∂μ = q' ^ m * (c0 - r ^ m * I) := by
    simp only [hg]
    rw [integral_const_mul, integral_sub (hind.const_mul _) (hφi.abs.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_indicator_const _ (measurableSet_ball : MeasurableSet B), smul_eq_mul, mul_one]
  have hpos : 0 < ∫ X, β X ^ m * φ X ∂μ := by
    have h1 := integral_mono hgi hβmφ hpt
    rw [hgint] at h1
    exact lt_of_lt_of_le (mul_pos (pow_pos hq'0 m) (by linarith)) h1
  -- but the integral vanishes
  have hFm : Integrable (fun X => ((β X : ℝ) : ℂ) ^ m * F X) μ := by
    refine Integrable.mono' hF.norm (((Complex.continuous_ofReal.comp hβc).pow m
      ).aestronglyMeasurable.mul hF.1) (ae_of_all _ fun X => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβpos X)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (hβpos X) (hβ1 X))
  have hzero' : ∫ X, β X ^ m * φ X ∂μ = 0 := by
    have e : (fun X => β X ^ m * φ X) =
        fun X => (starRingEnd ℂ a * (((β X : ℝ) : ℂ) ^ m * F X)).re := by
      funext X
      simp only [hφdef]
      rw [← Complex.ofReal_pow, mul_left_comm, Complex.re_ofReal_mul]
    have h2 := Complex.reCLM.integral_comp_comm (hFm.const_mul (starRingEnd ℂ a))
    simp only [Complex.reCLM_apply] at h2
    rw [e, h2, integral_const_mul, hzero m, mul_zero, Complex.zero_re]
  linarith

end Concentration

/-! ## The bump vectors in the pairing -/

attribute [local instance] measurableSpaceK

local instance borelSpaceK_ln (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

section Bump

variable {c : ℕ} {sz : Fin c → ℕ} {ds : List RealBlock}

/-- Multiplying `h` by `ω^m` multiplies the integrand of the pairing by `β^m`. -/
theorem psi_bump
    (hstrict : ∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p)
    {u f f' : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hu : Continuous u) (hf : Continuous f)
    (hf' : Continuous f') (m : ℕ)
    (hfg : ∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
      f' g = ((omega sz (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : ℝ) : ℂ) ^ m * f g)
    (κ : ∀ i, unitaryCompact ℝ (sz i)) (X : Coord sz → ℝ) :
    psi (slots ds (∑ i, sz i)) u f' κ X =
      ((beta sz X : ℝ) : ℂ) ^ m * psi (slots ds (∑ i, sz i)) u f κ X := by
  set L := slots ds (∑ i, sz i) with hLdef
  have hL := slots_cls_eq (sz := sz) hstrict
  rw [psi_eq_integral hu hf', psi_eq_integral hu hf, ← integral_const_mul]
  congr 1
  funext θ
  rw [hfg]
  have hω : omega sz ((torusElem L θ * (lowerGL sz X * bdK sz κ) :
      Langlands.GeneralLinear (∑ i, sz i) ℝ) : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
        beta sz X := by
    obtain ⟨h1, h2⟩ := mem_blockOrth_iff.mp (torusElem_mem_blockOrth L hL θ)
    obtain ⟨k1, k2⟩ := mem_blockOrth_iff.mp (bdK_mem_blockOrth (sz := sz) κ)
    rw [Units.val_mul, Units.val_mul, lowerGL_val, omega_mul_left sz h1 h2,
      omega_mul_right sz _ k1 k2]
    rfl
  rw [hω]
  ring

/-- Continuity of `X ↦ ∫_{K_M} psi(u, h)(κ, X) dκ`. -/
theorem continuous_integral_psi (L : List (Slot (∑ i, sz i)))
    {u h : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hu : Continuous u) (hh : Continuous h) :
    Continuous fun X : Coord sz → ℝ =>
      ∫ κ, psi L u h κ X ∂Measure.pi (fun i => haarK (sz i)) := by
  have hc := continuous_psi L hu hh
  have hc' : Continuous (Function.uncurry fun (X : Coord sz → ℝ)
      (κ : ∀ i, unitaryCompact ℝ (sz i)) => psi L u h κ X) :=
    Continuous.comp (g := fun p : (∀ i, unitaryCompact ℝ (sz i)) × (Coord sz → ℝ) =>
      psi L u h p.1 p.2) (f := Prod.swap) hc continuous_swap
  have := continuous_parametric_integral_of_continuous
    (μ := Measure.pi fun i => haarK (sz i)) hc' (isCompact_univ (X := ∀ i, unitaryCompact ℝ (sz i)))
  simpa only [Measure.restrict_univ] using this

variable (hT1 : RealLeviChartIntegrableStatement) (hA : Admissible sz ds)
  {u f : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ}
  (hu : u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i)
    (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ (∑ i, sz i)))
  (hf : f ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds)
    (unitaryCompact ℝ (∑ i, sz i)))
include hT1 hA hu hf

/-- `Θ(u, ω^m f) = ∫_X β(X)^m F(X) dX` with `F(X) = ∫_{K_M} psi(u, f)(κ, X) dκ`. -/
theorem theta_bump {f' : Langlands.GeneralLinear (∑ i, sz i) ℝ → ℂ} (hf' : Continuous f')
    (m : ℕ)
    (hfg : ∀ g : Langlands.GeneralLinear (∑ i, sz i) ℝ,
      f' g = ((omega sz (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : ℝ) : ℂ) ^ m * f g) :
    theta (slots ds (∑ i, sz i)) u f' = ∫ X, ((beta sz X : ℝ) : ℂ) ^ m *
      ∫ κ, psi (slots ds (∑ i, sz i)) u f κ X ∂Measure.pi (fun i => haarK (sz i)) := by
  have hpsi := integrable_psi_prod hT1 hA hu hf
  have hβ : Continuous fun X : Coord sz → ℝ => ((beta sz X : ℝ) : ℂ) ^ m :=
    (Complex.continuous_ofReal.comp continuous_beta).pow m
  have hint : Integrable (Function.uncurry fun (κ : ∀ i, unitaryCompact ℝ (sz i))
      (X : Coord sz → ℝ) => ((beta sz X : ℝ) : ℂ) ^ m * psi (slots ds (∑ i, sz i)) u f κ X)
      ((Measure.pi fun i => haarK (sz i)).prod volume) := by
    refine Integrable.mono' hpsi.norm ((hβ.comp continuous_snd).aestronglyMeasurable.mul
      hpsi.1) (ae_of_all _ fun p => ?_)
    show ‖((beta sz p.2 : ℝ) : ℂ) ^ m * psi (slots ds (∑ i, sz i)) u f p.1 p.2‖ ≤ _
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (beta_pos p.2).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (beta_pos p.2).le (beta_le_one p.2))
  unfold theta
  simp_rw [psi_bump hA.strict hu.1.1.continuous hf.1.1.1.continuous hf' m hfg]
  rw [integral_integral_swap hint]
  simp_rw [integral_const_mul]

/-- **Nonvanishing of the pairing.** If `∫_{K_M} psi(u, f)(κ, 0) dκ ≠ 0`, then `Θ(u, h) ≠ 0` for
some `O(N)`-finite vector `h` of the standard module. -/
theorem exists_theta_ne_zero
    (h0 : ∫ κ, psi (slots ds (∑ i, sz i)) u f κ 0 ∂Measure.pi (fun i => haarK (sz i)) ≠ 0) :
    ∃ h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i)),
      theta (slots ds (∑ i, sz i)) u h ≠ 0 := by
  by_contra hall
  push Not at hall
  refine h0 (concentration (μ := volume) continuous_beta beta_zero (fun X => (beta_pos X).le)
    beta_le_one (fun δ hδ => exists_gap hδ)
    (F := fun X => ∫ κ, psi (slots ds (∑ i, sz i)) u f κ X ∂Measure.pi (fun i => haarK (sz i)))
    ?_ ?_ fun m => ?_)
  · exact (integrable_psi_prod hT1 hA hu hf).integral_prod_right
  · exact (continuous_integral_psi (slots ds (∑ i, sz i)) hu.1.1.continuous
      hf.1.1.1.continuous).continuousAt
  · obtain ⟨f', hf', hfg⟩ := exists_bump_standard sz hA.rank hA.strict hf m
    rw [← theta_bump hT1 hA hu hf hf'.1.1.1.continuous m hfg]
    exact hall f' hf'

end Bump

end RealLeviNonvanishing

open RealInducedBlockBound RealInducedTorusCore RealLeviChart RealPrincipalSeriesDuality
  PartialJacquet RealInducedStandardBound RealStrictCharacterLanglandsQuotient in
attribute [local instance] measurableSpaceK in
/-- **Statement (nonvanishing of the pairing along `Q`).** Assume
`RealLeviChartIntegrableStatement`. Let `ds` be a list of real blocks of rank `N = ∑ sz_i` whose
block exponents decrease weakly along the positions and strictly from one block of `Q` to the
next, `u` an `O(N)`-finite vector of the principal series of the inverse characters and `f` an
`O(N)`-finite vector of the standard module of `ds`. If
`∫_{K_M} c_Z(x ↦ u(x diag(κ)) f(x diag(κ))) dκ ≠ 0`, then for some `O(N)`-finite vector `h` of
the standard module,
`∫_{K_M} ∫_{N̄_Q} c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ))) dX dκ ≠ 0`. -/
def RealLeviNonvanishingStatement : Prop :=
  RealLeviChartIntegrableStatement →
  ∀ (c : ℕ) (sz : Fin c → ℕ) (ds : List RealBlock), realRank ds = ∑ i, sz i →
    (∀ p q : Fin (∑ i, sz i), p ≤ q →
      realPositionBlockExponent ds q ≤ realPositionBlockExponent ds p) →
    (∀ p q : Fin (∑ i, sz i), cls sz p < cls sz q →
      realPositionBlockExponent ds q < realPositionBlockExponent ds p) →
    ∀ u ∈ kFiniteFunctions (principalSeries ℝ (∑ i, sz i) (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ (∑ i, sz i)),
    ∀ f ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i)),
      ∫ κ : (∀ i, unitaryCompact ℝ (sz i)), coeffs (zeroModes (slots ds (∑ i, sz i)))
          (fun x => u (x * blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))) *
            f (x * blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)))) 1
          ∂Measure.pi (fun i => haarK (sz i)) ≠ 0 →
      ∃ h ∈ kFiniteFunctions (realStandardModule (∑ i, sz i) ds) (unitaryCompact ℝ (∑ i, sz i)),
        ∫ κ : (∀ i, unitaryCompact ℝ (sz i)),
          (∫ X : Coord sz → ℝ, coeffs (zeroModes (slots ds (∑ i, sz i)))
            (fun x => u (x * blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))) *
              h (x * (lowerGL sz X *
                blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))))) 1)
          ∂Measure.pi (fun i => haarK (sz i)) ≠ 0

theorem realLeviNonvanishing : RealLeviNonvanishingStatement := by
  intro hT1 c sz ds hN hanti hstrict u hu f hf h0
  have e : ∀ κ : ∀ i, unitaryCompact ℝ (sz i),
      RealLeviPairing.psi (RealInducedStandardBound.slots ds (∑ i, sz i)) u f κ 0 =
        RealInducedBlockBound.coeffs
          (RealInducedTorusCore.zeroModes (RealInducedStandardBound.slots ds (∑ i, sz i)))
          (fun x => u (x * RealLeviChart.blockDiagGL sz
              (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ))) *
            f (x * RealLeviChart.blockDiagGL sz
              (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)))) 1 := by
    intro κ
    unfold RealLeviPairing.psi
    rw [RealLeviLimit.lowerGL_zero, one_mul]
    rfl
  obtain ⟨h, hh, hne⟩ := RealLeviNonvanishing.exists_theta_ne_zero hT1 ⟨hN, hanti, hstrict⟩ hu hf
    (by simp_rw [e]; exact h0)
  exact ⟨h, hh, hne⟩

end Langlands.Archimedean

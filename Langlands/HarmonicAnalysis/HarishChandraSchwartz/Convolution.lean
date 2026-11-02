import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TestFunctions
import Langlands.Representation.Hecke.Convolution

/-! # Convolution on the Harish-Chandra Schwartz space

Waldspurger 2003, Lemma III.6.1: for `f₁, f₂ ∈ C(G)` the integral
`f₁ * f₂ (g) = ∫_G f₁(h) f₂(h⁻¹ g) dh` converges absolutely for every `g`, the function
`f₁ * f₂` lies in `C(G)`, and the map `(f₁, f₂) ↦ f₁ * f₂` is separately continuous. The
weights `Ξ` and `σ` are arbitrary. The properties of the source weights used by the proof
(Lemmas II.1.3, II.1.4 and II.1.5, and the inequality
`1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))`) are explicit hypotheses.
-/

noncomputable section

open scoped ENNReal NNReal Topology
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

universe u

section Weights

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- The hypotheses on the weights used in the proof of Lemma III.6.1 of Waldspurger, for a
measure `μ` on `G` and a compact subgroup `K`:

* `Ξ` is positive and continuous, and `σ` is nonnegative and continuous;
* `1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))` for all `g, h`;
* `Ξ` and `σ` are invariant under left multiplication by `K`;
* `Ξ(g⁻¹) = Ξ(g)` (Lemma II.1.4);
* `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)` for the Haar measure of `K` of total mass one
  (Lemma II.1.3);
* there is `d ∈ ℕ` with `∫_G Ξ(g)² (1 + σ(g))^{-d} dμ(g) < ∞` (Lemma II.1.5). -/
structure ConvolutionWeights (μ : Measure G) (K : Subgroup G) [CompactSpace K]
    (Ξ σ : G → ℝ) : Prop where
  pos : ∀ g, 0 < Ξ g
  nonneg : ∀ g, 0 ≤ σ g
  continuous_xi : Continuous Ξ
  continuous_sigma : Continuous σ
  one_add_le : ∀ g h, 1 + σ g ≤ (1 + σ h) * (1 + σ (h⁻¹ * g))
  xi_mul_left : ∀ k ∈ K, ∀ g, Ξ (k * g) = Ξ g
  sigma_mul_left : ∀ k ∈ K, ∀ g, σ (k * g) = σ g
  xi_inv : ∀ g, Ξ g⁻¹ = Ξ g
  integral_xi : ∀ g₁ g₂, ∫ k : K, Ξ (g₁ * k * g₂) ∂(normalizedHaar K) = Ξ g₁ * Ξ g₂
  square : ∃ d : ℕ, ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))) ∂μ < ⊤

omit [IsTopologicalGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- A nonnegative subadditive `σ` satisfies `1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))`. -/
theorem one_add_le_of_le_add {σ : G → ℝ} (hσ : ∀ g, 0 ≤ σ g)
    (hadd : ∀ g h, σ (g * h) ≤ σ g + σ h) (g h : G) :
    1 + σ g ≤ (1 + σ h) * (1 + σ (h⁻¹ * g)) := by
  have h1 := hadd h (h⁻¹ * g)
  rw [mul_inv_cancel_left] at h1
  nlinarith [mul_nonneg (hσ h) (hσ (h⁻¹ * g))]

end Weights

section Pointwise

variable {G : Type u} {Ξ σ : G → ℝ}

/-- `weight Ξ σ r g · Ξ(g) (1 + σ(g))^{-r} = 1` for positive `Ξ` and nonnegative `σ`. -/
theorem weight_mul_ofReal (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (r : ℝ) (g : G) :
    weight Ξ σ r g * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) = 1 := by
  have hb : 0 < 1 + σ g := by linarith [hσ g]
  have hp : 0 < (1 + σ g) ^ r := Real.rpow_pos_of_pos hb r
  rw [weight, ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr (hΞ g).le) hp.le),
    Real.rpow_neg hb.le]
  have : (Ξ g)⁻¹ * (1 + σ g) ^ r * (Ξ g * ((1 + σ g) ^ r)⁻¹) = 1 := by
    field_simp [(hΞ g).ne', hp.ne']
  rw [this, ENNReal.ofReal_one]

/-- `|f(g)| ≤ ν_r(f) Ξ(g) (1 + σ(g))^{-r}`, in `ℝ≥0∞`. -/
theorem enorm_le_nu_mul (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (f : G → ℂ) (r : ℝ)
    (g : G) : ‖f g‖ₑ ≤ nu Ξ σ r f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) := by
  calc ‖f g‖ₑ = ‖f g‖ₑ * weight Ξ σ r g * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) := by
        rw [mul_assoc, weight_mul_ofReal hΞ hσ, mul_one]
    _ ≤ nu Ξ σ r f * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) := by
        gcongr
        exact enorm_mul_weight_le_nu f g

end Pointwise

section Convolution

variable {G : Type u} [Group G] [MeasurableSpace G]

/-- The convolution `(f₁ * f₂)(g) = ∫_G f₁(h) f₂(h⁻¹ g) dμ(h)` (Waldspurger III.6). It is a
Bochner integral, so it is `0` where the integrand is not integrable. -/
abbrev convolution (μ : Measure G) (f₁ f₂ : G → ℂ) (g : G) : ℂ :=
  Hecke.convolutionIntegral μ f₁ f₂ g

theorem convolution_apply (μ : Measure G) (f₁ f₂ : G → ℂ) (g : G) :
    convolution μ f₁ f₂ g = ∫ h, f₁ h * f₂ (h⁻¹ * g) ∂μ :=
  rfl

/-- For a left-invariant measure, the convolution of two `H`-bi-invariant functions is
`H`-bi-invariant. -/
theorem IsBiInvariant.convolution [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {H : Subgroup G} {f₁ f₂ : G → ℂ} (h₁ : IsBiInvariant H f₁) (h₂ : IsBiInvariant H f₂) :
    IsBiInvariant H (convolution μ f₁ f₂) := by
  intro k₁ hk₁ k₂ hk₂ g
  simp only [convolution_apply]
  rw [← integral_mul_left_eq_self _ k₁]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  simp only
  have e : (k₁ * h)⁻¹ * (k₁ * g * k₂) = 1 * (h⁻¹ * g) * k₂ := by group
  rw [e, h₂ 1 H.one_mem k₂ hk₂]
  have e' : k₁ * h = k₁ * h * 1 := (mul_one _).symm
  rw [e', h₁ k₁ hk₁ 1 H.one_mem]

theorem convolution_smul_left (μ : Measure G) (c : ℂ) (f₁ f₂ : G → ℂ) :
    convolution μ (c • f₁) f₂ = c • convolution μ f₁ f₂ := by
  funext g
  simp only [convolution_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem convolution_smul_right (μ : Measure G) (c : ℂ) (f₁ f₂ : G → ℂ) :
    convolution μ f₁ (c • f₂) = c • convolution μ f₁ f₂ := by
  funext g
  simp only [convolution_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

theorem convolution_add_left {μ : Measure G} {f₁ f₁' f₂ : G → ℂ}
    (h : ∀ g, Integrable (fun h => f₁ h * f₂ (h⁻¹ * g)) μ)
    (h' : ∀ g, Integrable (fun h => f₁' h * f₂ (h⁻¹ * g)) μ) :
    convolution μ (f₁ + f₁') f₂ = convolution μ f₁ f₂ + convolution μ f₁' f₂ := by
  funext g
  simp only [convolution_apply, Pi.add_apply, add_mul]
  exact integral_add (h g) (h' g)

theorem convolution_add_right {μ : Measure G} {f₁ f₂ f₂' : G → ℂ}
    (h : ∀ g, Integrable (fun h => f₁ h * f₂ (h⁻¹ * g)) μ)
    (h' : ∀ g, Integrable (fun h => f₁ h * f₂' (h⁻¹ * g)) μ) :
    convolution μ f₁ (f₂ + f₂') = convolution μ f₁ f₂ + convolution μ f₁ f₂' := by
  funext g
  simp only [convolution_apply, Pi.add_apply, mul_add]
  exact integral_add (h g) (h' g)

end Convolution

section Estimates

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]
  {K : Subgroup G} [CompactSpace K] {Ξ σ : G → ℝ}

namespace ConvolutionWeights

omit [SecondCountableTopology G] [μ.IsMulLeftInvariant] [SFinite μ] in
/-- For `r ≥ 0`: `(1 + σ(h⁻¹ g))^{-r} ≤ (1 + σ(g))^{-r} (1 + σ(h))^r`. -/
theorem rpow_le (hw : ConvolutionWeights μ K Ξ σ) {r : ℝ} (hr : 0 ≤ r) (g h : G) :
    (1 + σ (h⁻¹ * g)) ^ (-r) ≤ (1 + σ g) ^ (-r) * (1 + σ h) ^ r := by
  have ha : 0 < 1 + σ h := by linarith [hw.nonneg h]
  have hb : 0 < 1 + σ (h⁻¹ * g) := by linarith [hw.nonneg (h⁻¹ * g)]
  have hc : 0 < 1 + σ g := by linarith [hw.nonneg g]
  have h1 := Real.rpow_le_rpow_of_nonpos hc (hw.one_add_le g h) (neg_nonpos.mpr hr)
  rw [Real.mul_rpow ha.le hb.le] at h1
  have hp : 0 < (1 + σ h) ^ r := Real.rpow_pos_of_pos ha r
  calc (1 + σ (h⁻¹ * g)) ^ (-r)
      = (1 + σ h) ^ r * ((1 + σ h) ^ (-r) * (1 + σ (h⁻¹ * g)) ^ (-r)) := by
        rw [← mul_assoc, ← Real.rpow_add ha, add_neg_cancel, Real.rpow_zero, one_mul]
    _ ≤ (1 + σ h) ^ r * (1 + σ g) ^ (-r) := mul_le_mul_of_nonneg_left h1 hp.le
    _ = (1 + σ g) ^ (-r) * (1 + σ h) ^ r := mul_comm _ _

omit [SecondCountableTopology G] [μ.IsMulLeftInvariant] [SFinite μ] in
/-- The pointwise estimate of the integrand of `f₁ * f₂ (g)`, for `r ≥ 0`. -/
theorem enorm_mul_le (hw : ConvolutionWeights μ K Ξ σ) {r : ℝ} (hr : 0 ≤ r) (r' : ℝ)
    (f₁ f₂ : G → ℂ) (g h : G) :
    ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ≤
      nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ENNReal.ofReal ((1 + σ g) ^ (-r)) *
        ENNReal.ofReal (Ξ h * Ξ (h⁻¹ * g) * (1 + σ h) ^ (r - r')) := by
  set y := h⁻¹ * g
  have ha : 0 < 1 + σ h := by linarith [hw.nonneg h]
  have hb : 0 < 1 + σ y := by linarith [hw.nonneg y]
  have hA : 0 ≤ Ξ h * (1 + σ h) ^ (-r') :=
    mul_nonneg (hw.pos h).le (Real.rpow_nonneg ha.le _)
  have hreal : Ξ h * (1 + σ h) ^ (-r') * (Ξ y * (1 + σ y) ^ (-r)) ≤
      (1 + σ g) ^ (-r) * (Ξ h * Ξ y * (1 + σ h) ^ (r - r')) := by
    have h1 := hw.rpow_le hr g h
    have hB : 0 ≤ Ξ h * (1 + σ h) ^ (-r') * Ξ y :=
      mul_nonneg hA (hw.pos y).le
    calc Ξ h * (1 + σ h) ^ (-r') * (Ξ y * (1 + σ y) ^ (-r))
        = Ξ h * (1 + σ h) ^ (-r') * Ξ y * (1 + σ y) ^ (-r) := by ring
      _ ≤ Ξ h * (1 + σ h) ^ (-r') * Ξ y * ((1 + σ g) ^ (-r) * (1 + σ h) ^ r) :=
          mul_le_mul_of_nonneg_left h1 hB
      _ = (1 + σ g) ^ (-r) * (Ξ h * Ξ y * ((1 + σ h) ^ (-r') * (1 + σ h) ^ r)) := by ring
      _ = (1 + σ g) ^ (-r) * (Ξ h * Ξ y * (1 + σ h) ^ (r - r')) := by
          rw [← Real.rpow_add ha, neg_add_eq_sub]
  calc ‖f₁ h‖ₑ * ‖f₂ y‖ₑ
      ≤ (nu Ξ σ r' f₁ * ENNReal.ofReal (Ξ h * (1 + σ h) ^ (-r'))) *
          (nu Ξ σ r f₂ * ENNReal.ofReal (Ξ y * (1 + σ y) ^ (-r))) :=
        mul_le_mul' (enorm_le_nu_mul hw.pos hw.nonneg f₁ r' h)
          (enorm_le_nu_mul hw.pos hw.nonneg f₂ r y)
    _ = nu Ξ σ r' f₁ * nu Ξ σ r f₂ *
          ENNReal.ofReal (Ξ h * (1 + σ h) ^ (-r') * (Ξ y * (1 + σ y) ^ (-r))) := by
        rw [ENNReal.ofReal_mul hA]
        ring
    _ ≤ nu Ξ σ r' f₁ * nu Ξ σ r f₂ *
          ENNReal.ofReal ((1 + σ g) ^ (-r) * (Ξ h * Ξ y * (1 + σ h) ^ (r - r'))) := by
        gcongr
    _ = nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ENNReal.ofReal ((1 + σ g) ^ (-r)) *
          ENNReal.ofReal (Ξ h * Ξ y * (1 + σ h) ^ (r - r')) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hw.nonneg g]) _)]
        ring

omit [SecondCountableTopology G] [μ.IsMulLeftInvariant] [SFinite μ] in
theorem measurable_aux (hw : ConvolutionWeights μ K Ξ σ) (s : ℝ) (g : G) :
    Measurable fun h => ENNReal.ofReal (Ξ h * Ξ (h⁻¹ * g) * (1 + σ h) ^ s) := by
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  have hσ : Continuous fun h => (1 + σ h) ^ s :=
    (continuous_const.add hw.continuous_sigma).rpow_const fun h =>
      Or.inl (ne_of_gt (show 0 < 1 + σ h by linarith [hw.nonneg h]))
  exact (hw.continuous_xi.mul (hw.continuous_xi.comp (continuous_inv.mul continuous_const))).mul hσ

/-- The `K`-averaging step of the proof of Lemma III.6.1: replacing `h` by `k⁻¹ h`,
integrating over `k ∈ K`, and using Lemmas II.1.3 and II.1.4,
`∫_G Ξ(h) Ξ(h⁻¹ g) (1 + σ(h))^s dh = Ξ(g) ∫_G Ξ(h)² (1 + σ(h))^s dh`. -/
theorem lintegral_xi_mul_xi (hw : ConvolutionWeights μ K Ξ σ) (s : ℝ) (g : G) :
    ∫⁻ h, ENNReal.ofReal (Ξ h * Ξ (h⁻¹ * g) * (1 + σ h) ^ s) ∂μ =
      ENNReal.ofReal (Ξ g) * ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ s) ∂μ := by
  set ν := normalizedHaar K
  set F : G → ℝ≥0∞ := fun h => ENNReal.ofReal (Ξ h * Ξ (h⁻¹ * g) * (1 + σ h) ^ s) with hF
  have hσc : Continuous fun h => (1 + σ h) ^ s :=
    (continuous_const.add hw.continuous_sigma).rpow_const fun h =>
      Or.inl (ne_of_gt (show 0 < 1 + σ h by linarith [hw.nonneg h]))
  -- translating by `k⁻¹` for `k ∈ K`
  have htrans : ∀ k : K, ∫⁻ h, F h ∂μ =
      ∫⁻ h, ENNReal.ofReal (Ξ h * (1 + σ h) ^ s * Ξ (h⁻¹ * k * g)) ∂μ := by
    intro k
    rw [← lintegral_mul_left_eq_self F (k : G)⁻¹]
    refine lintegral_congr fun h => ?_
    have hk : (k : G)⁻¹ ∈ K := K.inv_mem k.2
    simp only [hF]
    rw [hw.xi_mul_left _ hk, hw.sigma_mul_left _ hk, mul_inv_rev, inv_inv]
    congr 1
    rw [mul_assoc h⁻¹]
    ring
  -- averaging over `K`
  have havg : ∫⁻ h, F h ∂μ =
      ∫⁻ k : K, ∫⁻ h, ENNReal.ofReal (Ξ h * (1 + σ h) ^ s * Ξ (h⁻¹ * k * g)) ∂μ ∂ν := by
    simp_rw [← htrans]
    rw [lintegral_const, measure_univ, mul_one]
  -- Tonelli
  have hmeas : AEMeasurable (Function.uncurry fun (k : K) (h : G) =>
      ENNReal.ofReal (Ξ h * (1 + σ h) ^ s * Ξ (h⁻¹ * k * g))) (ν.prod μ) := by
    refine (ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)).aemeasurable
    exact ((hw.continuous_xi.comp continuous_snd).mul (hσc.comp continuous_snd)).mul
      (hw.continuous_xi.comp (((continuous_inv.comp continuous_snd).mul
        (continuous_subtype_val.comp continuous_fst)).mul continuous_const))
  rw [havg, lintegral_lintegral_swap hmeas]
  -- the inner integral over `K`, by Lemmas II.1.3 and II.1.4
  have hinner : ∀ h : G, ∫⁻ k : K, ENNReal.ofReal (Ξ h * (1 + σ h) ^ s * Ξ (h⁻¹ * k * g)) ∂ν =
      ENNReal.ofReal (Ξ g) * ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ s) := by
    intro h
    have hA : 0 ≤ Ξ h * (1 + σ h) ^ s :=
      mul_nonneg (hw.pos h).le (Real.rpow_nonneg (by linarith [hw.nonneg h]) _)
    simp_rw [ENNReal.ofReal_mul hA]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hc : Continuous fun k : K => Ξ (h⁻¹ * k * g) :=
      hw.continuous_xi.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
    have hint : Integrable (fun k : K => Ξ (h⁻¹ * k * g)) ν :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun k => (hw.pos _).le), hw.integral_xi, hw.xi_inv,
      ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (hw.pos g).le]
    congr 1
    ring
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The main estimate of the proof of Lemma III.6.1: for `r ≥ 0` and all `r'`,
`∫_G |f₁(h) f₂(h⁻¹ g)| dh ≤ ν_{r'}(f₁) ν_r(f₂) Ξ(g) (1 + σ(g))^{-r} ∫_G Ξ(h)² (1 + σ(h))^{r - r'} dh`. -/
theorem lintegral_enorm_mul_le (hw : ConvolutionWeights μ K Ξ σ) {r : ℝ} (hr : 0 ≤ r)
    (r' : ℝ) (f₁ f₂ : G → ℂ) (g : G) :
    ∫⁻ h, ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ∂μ ≤
      nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) *
        ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (r - r')) ∂μ := by
  calc ∫⁻ h, ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ∂μ
      ≤ ∫⁻ h, nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ENNReal.ofReal ((1 + σ g) ^ (-r)) *
          ENNReal.ofReal (Ξ h * Ξ (h⁻¹ * g) * (1 + σ h) ^ (r - r')) ∂μ :=
        lintegral_mono fun h => hw.enorm_mul_le hr r' f₁ f₂ g h
    _ = nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ENNReal.ofReal ((1 + σ g) ^ (-r)) *
          ∫⁻ h, ENNReal.ofReal (Ξ h * Ξ (h⁻¹ * g) * (1 + σ h) ^ (r - r')) ∂μ :=
        lintegral_const_mul _ (hw.measurable_aux _ g)
    _ = nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) *
          ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (r - r')) ∂μ := by
        rw [hw.lintegral_xi_mul_xi, ENNReal.ofReal_mul (hw.pos g).le]
        ring

/-- The estimate `ν_r(f₁ * f₂) ≤ ν_{r'}(f₁) ν_r(f₂) ∫_G Ξ(h)² (1 + σ(h))^{r - r'} dh` for
`r ≥ 0`. -/
theorem nu_convolution_le (hw : ConvolutionWeights μ K Ξ σ) {r : ℝ} (hr : 0 ≤ r) (r' : ℝ)
    (f₁ f₂ : G → ℂ) :
    nu Ξ σ r (convolution μ f₁ f₂) ≤
      nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (r - r')) ∂μ := by
  refine iSup_le fun g => ?_
  have h1 : ‖convolution μ f₁ f₂ g‖ₑ ≤ ∫⁻ h, ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ∂μ := by
    rw [convolution_apply]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_mul]
  calc ‖convolution μ f₁ f₂ g‖ₑ * weight Ξ σ r g
      ≤ (nu Ξ σ r' f₁ * nu Ξ σ r f₂ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) *
          ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (r - r')) ∂μ) * weight Ξ σ r g := by
        gcongr
        exact h1.trans (hw.lintegral_enorm_mul_le hr r' f₁ f₂ g)
    _ = nu Ξ σ r' f₁ * nu Ξ σ r f₂ *
          (∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (r - r')) ∂μ) *
          (weight Ξ σ r g * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r))) := by ring
    _ = nu Ξ σ r' f₁ * nu Ξ σ r f₂ *
          ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (r - r')) ∂μ := by
        rw [weight_mul_ofReal hw.pos hw.nonneg, mul_one]

/-- The constant of Lemma II.1.5: `∫_G Ξ(h)² (1 + σ(h))^{-d} dh` for the exponent `d`
chosen in `ConvolutionWeights.square`. -/
def squareExponent (hw : ConvolutionWeights μ K Ξ σ) : ℕ :=
  hw.square.choose

omit [SecondCountableTopology G] [μ.IsMulLeftInvariant] [SFinite μ] in
theorem lintegral_square_lt_top (hw : ConvolutionWeights μ K Ξ σ) :
    ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (-(hw.squareExponent : ℝ))) ∂μ < ⊤ :=
  hw.square.choose_spec

/-- With `d` from Lemma II.1.5: `ν_r(f₁ * f₂) ≤ c ν_{r+d}(f₁) ν_r(f₂)` for `r ≥ 0`, with
`c = ∫_G Ξ(h)² (1 + σ(h))^{-d} dh < ∞` (the last display of the proof of Lemma III.6.1). -/
theorem nu_convolution_le_square (hw : ConvolutionWeights μ K Ξ σ) {r : ℝ} (hr : 0 ≤ r)
    (f₁ f₂ : G → ℂ) :
    nu Ξ σ r (convolution μ f₁ f₂) ≤
      nu Ξ σ (r + hw.squareExponent) f₁ * nu Ξ σ r f₂ *
        ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (-(hw.squareExponent : ℝ))) ∂μ := by
  have h := hw.nu_convolution_le hr (r + hw.squareExponent) f₁ f₂
  rwa [sub_add_cancel_left] at h

/-- Absolute convergence of the convolution integral (first assertion of Lemma III.6.1):
if `f₁` and `f₂` are continuous with `ν_d(f₁) < ∞` and `ν_0(f₂) < ∞`, then
`h ↦ f₁(h) f₂(h⁻¹ g)` is integrable for every `g`. -/
theorem integrable_mul (hw : ConvolutionWeights μ K Ξ σ) {f₁ f₂ : G → ℂ}
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂)
    (h₁ : nu Ξ σ hw.squareExponent f₁ < ⊤) (h₂ : nu Ξ σ 0 f₂ < ⊤) (g : G) :
    Integrable (fun h => f₁ h * f₂ (h⁻¹ * g)) μ := by
  refine ⟨(hc₁.mul (hc₂.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable, ?_⟩
  have h := hw.lintegral_enorm_mul_le le_rfl hw.squareExponent f₁ f₂ g
  rw [zero_sub] at h
  simp only [HasFiniteIntegral, enorm_mul]
  refine lt_of_le_of_lt h ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top h₁ h₂)
    ENNReal.ofReal_lt_top) hw.lintegral_square_lt_top

/-- `ν_r(f₁ * f₂) ≤ c ν_{r₀+d}(f₁) ν_{r₀}(f₂)` for all `r`, with `r₀ = max r 0`. -/
theorem nu_convolution_le_max (hw : ConvolutionWeights μ K Ξ σ) (r : ℝ) (f₁ f₂ : G → ℂ) :
    nu Ξ σ r (convolution μ f₁ f₂) ≤
      nu Ξ σ (max r 0 + hw.squareExponent) f₁ * nu Ξ σ (max r 0) f₂ *
        ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (-(hw.squareExponent : ℝ))) ∂μ :=
  (nu_mono hw.nonneg (le_max_left r 0) _).trans
    (hw.nu_convolution_le_square (le_max_right r 0) f₁ f₂)

end ConvolutionWeights

end Estimates

section Levels

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]
  {K : Subgroup G} [CompactSpace K] {Ξ σ : G → ℝ}

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- An element of a level `C_H` is continuous. -/
theorem continuous_of_mem_levelSubmodule {H : CompactOpenSubgroup G} {f : G → ℂ}
    (hf : f ∈ levelSubmodule Ξ σ H.toSubgroup) : Continuous f :=
  (IsBiInvariant.isLocallyConstant (K := H) hf.1).continuous

namespace ConvolutionWeights

/-- The convolution integrand of two elements of a level `C_H` is integrable. -/
theorem integrable_mul_of_mem (hw : ConvolutionWeights μ K Ξ σ) {H₁ H₂ : CompactOpenSubgroup G}
    {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ levelSubmodule Ξ σ H₁.toSubgroup)
    (h₂ : f₂ ∈ levelSubmodule Ξ σ H₂.toSubgroup) (g : G) :
    Integrable (fun h => f₁ h * f₂ (h⁻¹ * g)) μ :=
  hw.integrable_mul (continuous_of_mem_levelSubmodule h₁) (continuous_of_mem_levelSubmodule h₂)
    (h₁.2 _) (h₂.2 _) g

/-- Lemma III.6.1 on a level: the convolution of two elements of `C_H` lies in `C_H`. -/
theorem convolution_mem_levelSubmodule (hw : ConvolutionWeights μ K Ξ σ)
    {H : CompactOpenSubgroup G} {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ levelSubmodule Ξ σ H.toSubgroup)
    (h₂ : f₂ ∈ levelSubmodule Ξ σ H.toSubgroup) :
    convolution μ f₁ f₂ ∈ levelSubmodule Ξ σ H.toSubgroup := by
  refine ⟨h₁.1.convolution h₂.1, fun r => ?_⟩
  refine lt_of_le_of_lt (hw.nu_convolution_le_max r f₁ f₂) ?_
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (h₁.2 _) (h₂.2 _)) hw.lintegral_square_lt_top

end ConvolutionWeights

end Levels

section Operators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]
  {K : Subgroup G} [CompactSpace K] {Ξ σ : G → ℝ}

namespace Level

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- A linear map between levels is continuous if every `ν_r` of the image is bounded by a
finite multiple of some `ν_s`. -/
theorem continuous_of_nu_le {H₁ H₂ : CompactOpenSubgroup G}
    (T : Level Ξ σ H₁ →ₗ[ℂ] Level Ξ σ H₂)
    (hT : ∀ r : ℝ, ∃ s : ℝ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f, nu Ξ σ r (T f) ≤ C * nu Ξ σ s f) :
    Continuous T := by
  refine (withSeminorms H₁).continuous_of_isBounded (withSeminorms H₂) _ ?_
  refine Seminorm.IsBounded.of_real fun r => ?_
  obtain ⟨s, C, hC, h⟩ := hT r
  refine ⟨{s}, C.toReal, fun f => ?_⟩
  rw [Finset.sup_singleton]
  change (nu Ξ σ r (T f)).toReal ≤ C.toReal * (nu Ξ σ s f).toReal
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hC (nu_ne_top f s)) (h f)

/-- For `f₂ ∈ C_{H₂}`, the map `f₁ ↦ f₁ * f₂` from `C_{H₁}` to `C_{H₁ ∩ H₂}`. -/
def convolutionLeft (hw : ConvolutionWeights μ K Ξ σ) {H₂ : CompactOpenSubgroup G}
    {f₂ : G → ℂ} (h₂ : f₂ ∈ levelSubmodule Ξ σ H₂.toSubgroup) (H₁ : CompactOpenSubgroup G) :
    Level Ξ σ H₁ →ₗ[ℂ] Level Ξ σ (H₁.inf H₂) where
  toFun f := (⟨convolution μ f f₂, hw.convolution_mem_levelSubmodule
      (levelSubmodule_antitone Ξ σ (H₁.inf_le_left H₂) (f : levelSubmodule Ξ σ H₁.toSubgroup).2)
      (levelSubmodule_antitone Ξ σ (H₁.inf_le_right H₂) h₂)⟩ :
    levelSubmodule Ξ σ (H₁.inf H₂).toSubgroup)
  map_add' f f' := Level.ext fun g => congrFun (convolution_add_left
      (hw.integrable_mul_of_mem (f : levelSubmodule Ξ σ H₁.toSubgroup).2 h₂)
      (hw.integrable_mul_of_mem (f' : levelSubmodule Ξ σ H₁.toSubgroup).2 h₂)) g
  map_smul' c f := Level.ext fun g => congrFun (convolution_smul_left μ c f f₂) g

@[simp] theorem coe_convolutionLeft (hw : ConvolutionWeights μ K Ξ σ)
    {H₂ : CompactOpenSubgroup G} {f₂ : G → ℂ} (h₂ : f₂ ∈ levelSubmodule Ξ σ H₂.toSubgroup)
    (H₁ : CompactOpenSubgroup G) (f : Level Ξ σ H₁) :
    ((convolutionLeft hw h₂ H₁ f : Level Ξ σ (H₁.inf H₂)) : G → ℂ) = convolution μ f f₂ :=
  rfl

/-- For `f₁ ∈ C_{H₁}`, the map `f₂ ↦ f₁ * f₂` from `C_{H₂}` to `C_{H₁ ∩ H₂}`. -/
def convolutionRight (hw : ConvolutionWeights μ K Ξ σ) {H₁ : CompactOpenSubgroup G}
    {f₁ : G → ℂ} (h₁ : f₁ ∈ levelSubmodule Ξ σ H₁.toSubgroup) (H₂ : CompactOpenSubgroup G) :
    Level Ξ σ H₂ →ₗ[ℂ] Level Ξ σ (H₁.inf H₂) where
  toFun f := (⟨convolution μ f₁ f, hw.convolution_mem_levelSubmodule
      (levelSubmodule_antitone Ξ σ (H₁.inf_le_left H₂) h₁)
      (levelSubmodule_antitone Ξ σ (H₁.inf_le_right H₂)
        (f : levelSubmodule Ξ σ H₂.toSubgroup).2)⟩ :
    levelSubmodule Ξ σ (H₁.inf H₂).toSubgroup)
  map_add' f f' := Level.ext fun g => congrFun (convolution_add_right
      (hw.integrable_mul_of_mem h₁ (f : levelSubmodule Ξ σ H₂.toSubgroup).2)
      (hw.integrable_mul_of_mem h₁ (f' : levelSubmodule Ξ σ H₂.toSubgroup).2)) g
  map_smul' c f := Level.ext fun g => congrFun (convolution_smul_right μ c f₁ f) g

@[simp] theorem coe_convolutionRight (hw : ConvolutionWeights μ K Ξ σ)
    {H₁ : CompactOpenSubgroup G} {f₁ : G → ℂ} (h₁ : f₁ ∈ levelSubmodule Ξ σ H₁.toSubgroup)
    (H₂ : CompactOpenSubgroup G) (f : Level Ξ σ H₂) :
    ((convolutionRight hw h₁ H₂ f : Level Ξ σ (H₁.inf H₂)) : G → ℂ) = convolution μ f₁ f :=
  rfl

/-- `f₁ ↦ f₁ * f₂` is continuous from `C_{H₁}` to `C_{H₁ ∩ H₂}`. -/
theorem continuous_convolutionLeft (hw : ConvolutionWeights μ K Ξ σ)
    {H₂ : CompactOpenSubgroup G} {f₂ : G → ℂ} (h₂ : f₂ ∈ levelSubmodule Ξ σ H₂.toSubgroup)
    (H₁ : CompactOpenSubgroup G) : Continuous (convolutionLeft hw h₂ H₁) := by
  refine continuous_of_nu_le _ fun r => ⟨max r 0 + hw.squareExponent,
    nu Ξ σ (max r 0) f₂ *
      ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (-(hw.squareExponent : ℝ))) ∂μ,
    ENNReal.mul_ne_top (h₂.2 _).ne hw.lintegral_square_lt_top.ne, fun f => ?_⟩
  exact (hw.nu_convolution_le_max r f f₂).trans_eq (by ring)

/-- `f₂ ↦ f₁ * f₂` is continuous from `C_{H₂}` to `C_{H₁ ∩ H₂}`. -/
theorem continuous_convolutionRight (hw : ConvolutionWeights μ K Ξ σ)
    {H₁ : CompactOpenSubgroup G} {f₁ : G → ℂ} (h₁ : f₁ ∈ levelSubmodule Ξ σ H₁.toSubgroup)
    (H₂ : CompactOpenSubgroup G) : Continuous (convolutionRight hw h₁ H₂) := by
  refine continuous_of_nu_le _ fun r => ⟨max r 0,
    nu Ξ σ (max r 0 + hw.squareExponent) f₁ *
      ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (-(hw.squareExponent : ℝ))) ∂μ,
    ENNReal.mul_ne_top (h₁.2 _).ne hw.lintegral_square_lt_top.ne, fun f => ?_⟩
  exact (hw.nu_convolution_le_max r f₁ f).trans_eq (by ring)

end Level

variable [Nonempty (CompactOpenSubgroup G)]

namespace ConvolutionWeights

/-- Absolute convergence of the convolution integral for `f₁, f₂ ∈ C(G)` (Lemma III.6.1). -/
theorem integrable_mul_of_mem_schwartzSubmodule (hw : ConvolutionWeights μ K Ξ σ)
    {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ schwartzSubmodule Ξ σ) (h₂ : f₂ ∈ schwartzSubmodule Ξ σ)
    (g : G) : Integrable (fun h => f₁ h * f₂ (h⁻¹ * g)) μ := by
  obtain ⟨H₁, h₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp h₁
  obtain ⟨H₂, h₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp h₂
  exact hw.integrable_mul_of_mem h₁ h₂ g

/-- Lemma III.6.1: `C(G)` is stable under convolution. -/
theorem convolution_mem_schwartzSubmodule (hw : ConvolutionWeights μ K Ξ σ)
    {f₁ f₂ : G → ℂ} (h₁ : f₁ ∈ schwartzSubmodule Ξ σ) (h₂ : f₂ ∈ schwartzSubmodule Ξ σ) :
    convolution μ f₁ f₂ ∈ schwartzSubmodule Ξ σ := by
  obtain ⟨H₁, h₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp h₁
  obtain ⟨H₂, h₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp h₂
  exact levelSubmodule_le_schwartzSubmodule Ξ σ (H₁.inf H₂)
    (hw.convolution_mem_levelSubmodule
      (levelSubmodule_antitone Ξ σ (H₁.inf_le_left H₂) h₁)
      (levelSubmodule_antitone Ξ σ (H₁.inf_le_right H₂) h₂))

end ConvolutionWeights

namespace Space

/-- The convolution product `f₁ * f₂` on `C(G)` (Lemma III.6.1). -/
def convolution (hw : ConvolutionWeights μ K Ξ σ) (f₁ f₂ : Space Ξ σ) : Space Ξ σ :=
  (⟨HarishChandraSchwartz.convolution μ f₁ f₂,
    hw.convolution_mem_schwartzSubmodule (coe_mem f₁) (coe_mem f₂)⟩ : schwartzSubmodule Ξ σ)

@[simp] theorem coe_convolution (hw : ConvolutionWeights μ K Ξ σ) (f₁ f₂ : Space Ξ σ) :
    ((convolution hw f₁ f₂ : Space Ξ σ) : G → ℂ) = HarishChandraSchwartz.convolution μ f₁ f₂ :=
  rfl

/-- The convolution product on `C(G)` as a bilinear map. -/
def convolutionBilin (hw : ConvolutionWeights μ K Ξ σ) :
    Space Ξ σ →ₗ[ℂ] Space Ξ σ →ₗ[ℂ] Space Ξ σ :=
  LinearMap.mk₂ ℂ (convolution hw)
    (fun f₁ f₁' f₂ => ext fun g => congrFun (convolution_add_left
      (hw.integrable_mul_of_mem_schwartzSubmodule (coe_mem f₁) (coe_mem f₂))
      (hw.integrable_mul_of_mem_schwartzSubmodule (coe_mem f₁') (coe_mem f₂))) g)
    (fun c f₁ f₂ => ext fun g => congrFun (convolution_smul_left μ c f₁ f₂) g)
    (fun f₁ f₂ f₂' => ext fun g => congrFun (convolution_add_right
      (hw.integrable_mul_of_mem_schwartzSubmodule (coe_mem f₁) (coe_mem f₂))
      (hw.integrable_mul_of_mem_schwartzSubmodule (coe_mem f₁) (coe_mem f₂'))) g)
    (fun c f₁ f₂ => ext fun g => congrFun (convolution_smul_right μ c f₁ f₂) g)

@[simp] theorem convolutionBilin_apply (hw : ConvolutionWeights μ K Ξ σ) (f₁ f₂ : Space Ξ σ) :
    convolutionBilin hw f₁ f₂ = convolution hw f₁ f₂ :=
  rfl

/-- Lemma III.6.1, separate continuity in the first variable: for fixed `f₂ ∈ C(G)`,
`f₁ ↦ f₁ * f₂` is continuous on `C(G)`. -/
theorem continuous_convolution_left (hw : ConvolutionWeights μ K Ξ σ) (f₂ : Space Ξ σ) :
    Continuous fun f₁ : Space Ξ σ => convolution hw f₁ f₂ := by
  obtain ⟨H₂, h₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f₂)
  refine (continuous_iff_continuous_comp ((convolutionBilin hw).flip f₂)).mpr fun H₁ => ?_
  have e : ((convolutionBilin hw).flip f₂ ∘ ofLevel H₁ : Level Ξ σ H₁ → Space Ξ σ) =
      ofLevel (H₁.inf H₂) ∘ Level.convolutionLeft hw h₂ H₁ :=
    funext fun _ => ext fun _ => rfl
  rw [e]
  exact (continuous_ofLevel _).comp (Level.continuous_convolutionLeft hw h₂ H₁)

/-- Lemma III.6.1, separate continuity in the second variable: for fixed `f₁ ∈ C(G)`,
`f₂ ↦ f₁ * f₂` is continuous on `C(G)`. -/
theorem continuous_convolution_right (hw : ConvolutionWeights μ K Ξ σ) (f₁ : Space Ξ σ) :
    Continuous fun f₂ : Space Ξ σ => convolution hw f₁ f₂ := by
  obtain ⟨H₁, h₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f₁)
  refine (continuous_iff_continuous_comp (convolutionBilin hw f₁)).mpr fun H₂ => ?_
  have e : (convolutionBilin hw f₁ ∘ ofLevel H₂ : Level Ξ σ H₂ → Space Ξ σ) =
      ofLevel (H₁.inf H₂) ∘ Level.convolutionRight hw h₁ H₂ :=
    funext fun _ => ext fun _ => rfl
  rw [e]
  exact (continuous_ofLevel _).comp (Level.continuous_convolutionRight hw h₁ H₂)

end Space

end Operators

end Langlands.HarishChandraSchwartz

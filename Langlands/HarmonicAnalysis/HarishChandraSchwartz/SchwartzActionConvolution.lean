import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations

/-! # `π(f₁ * f₂) = π(f₁) π(f₂)` for `f₁, f₂ ∈ C(G)` (III.7)

For `f₁, f₂ ∈ C(G)` and a continuous `φ` of tempered growth, the function
`(h, g) ↦ f₁(h) f₂(h⁻¹ g) φ(g)` is integrable on `G × G`, so that Fubini's theorem gives
`∫_G (f₁ * f₂)(g) φ(g) dg = ∫_G f₁(h) ∫_G f₂(y) φ(h y) dy dh`. Applied to the coefficients
`φ(g) = ℓ(ρ(g) v)` of an admissible representation with tempered coefficients this is the
identity `π(f₁ * f₂) = π(f₁) π(f₂)` of Waldspurger III.7. The operators also intertwine
translations: `π(f(a⁻¹ ·)) = ρ(a) π(f)`, and `π(f(· a)) = π(f) ρ(a⁻¹)` for a right invariant
measure, where `ρ` is the representation on `V` and `π(f) = schwartzAction hw hρ hT f`.
-/

noncomputable section

universe u v

open scoped ENNReal
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

section Fubini

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]
  {K : Subgroup G} [CompactSpace K] {Ξ σ : G → ℝ}

/-- The integrand `(h, g) ↦ f₁(h) f₂(h⁻¹ g) φ(g)` on `G × G` of the double integral
`∫_G ∫_G f₁(h) f₂(h⁻¹ g) φ(g) dh dg`, whose inner integral over `h` is `(f₁ * f₂)(g) φ(g)`. -/
def convolutionIntegrand (f₁ f₂ φ : G → ℂ) (z : G × G) : ℂ :=
  f₁ z.1 * f₂ (z.1⁻¹ * z.2) * φ z.2

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
@[simp]
theorem convolutionIntegrand_apply (f₁ f₂ φ : G → ℂ) (h g : G) :
    convolutionIntegrand f₁ f₂ φ (h, g) = f₁ h * f₂ (h⁻¹ * g) * φ g :=
  rfl

namespace ConvolutionWeights

/-- For `f₁, f₂` with all `ν_r` finite and `φ` with `ν_s(φ) < ∞` for some `s`,
`∫_G (∫_G |f₁(h)| |f₂(h⁻¹ g)| dh) |φ(g)| dg < ∞`. -/
theorem lintegral_lintegral_enorm_mul_lt_top (hw : ConvolutionWeights μ K Ξ σ)
    {f₁ f₂ φ : G → ℂ} (h₁ : ∀ r, nu Ξ σ r f₁ ≠ ⊤) (h₂ : ∀ r, nu Ξ σ r f₂ ≠ ⊤) {s : ℝ}
    (hφ : nu Ξ σ s φ ≠ ⊤) :
    ∫⁻ g, (∫⁻ h, ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ∂μ) * ‖φ g‖ₑ ∂μ < ⊤ := by
  set d : ℝ := (hw.squareExponent : ℝ)
  set s' : ℝ := min s d
  set r : ℝ := d - s'
  have hr : 0 ≤ r := sub_nonneg.mpr (min_le_right s d)
  have hφ' : nu Ξ σ s' φ ≠ ⊤ := ne_top_of_le_ne_top hφ (nu_mono hw.nonneg (min_le_left s d) φ)
  set I := ∫⁻ h, ENNReal.ofReal (Ξ h ^ 2 * (1 + σ h) ^ (-d)) ∂μ
  set C := nu Ξ σ (r + d) f₁ * nu Ξ σ r f₂ * I * nu Ξ σ s' φ
  have hC : C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (h₁ _) (h₂ _))
      hw.lintegral_square_lt_top.ne) hφ'
  have hpt : ∀ g, (∫⁻ h, ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ∂μ) * ‖φ g‖ₑ ≤
      C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) := by
    intro g
    have hin := hw.lintegral_enorm_mul_le hr (r + d) f₁ f₂ g
    rw [sub_add_cancel_left] at hin
    have hb : 0 < 1 + σ g := by linarith [hw.nonneg g]
    have hA : 0 ≤ Ξ g * (1 + σ g) ^ (-r) := mul_nonneg (hw.pos g).le (Real.rpow_nonneg hb.le _)
    have he : Ξ g * (1 + σ g) ^ (-r) * (Ξ g * (1 + σ g) ^ (-s')) =
        Ξ g ^ 2 * (1 + σ g) ^ (-d) := by
      have hd : -d = -r + -s' := by simp only [r]; ring
      rw [hd, Real.rpow_add hb]
      ring
    calc (∫⁻ h, ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ∂μ) * ‖φ g‖ₑ
        ≤ (nu Ξ σ (r + d) f₁ * nu Ξ σ r f₂ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) * I) *
            (nu Ξ σ s' φ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-s'))) :=
          mul_le_mul' hin (enorm_le_nu_mul hw.pos hw.nonneg φ s' g)
      _ = C * (ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r)) *
            ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-s'))) := by
          simp only [C]
          ring
      _ = C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) := by
          rw [← ENNReal.ofReal_mul hA, he]
  calc ∫⁻ g, (∫⁻ h, ‖f₁ h‖ₑ * ‖f₂ (h⁻¹ * g)‖ₑ ∂μ) * ‖φ g‖ₑ ∂μ
      ≤ ∫⁻ g, C * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) ∂μ := lintegral_mono hpt
    _ = C * I := lintegral_const_mul' _ _ hC
    _ < ⊤ := ENNReal.mul_lt_top hC.lt_top hw.lintegral_square_lt_top

/-- For continuous `f₁, f₂` with all `ν_r` finite and continuous `φ` with `ν_s(φ) < ∞`,
the function `convolutionIntegrand f₁ f₂ φ : (h, g) ↦ f₁(h) f₂(h⁻¹ g) φ(g)` is integrable on
`G × G`. -/
theorem integrable_prod (hw : ConvolutionWeights μ K Ξ σ) {f₁ f₂ φ : G → ℂ}
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (hφc : Continuous φ)
    (h₁ : ∀ r, nu Ξ σ r f₁ ≠ ⊤) (h₂ : ∀ r, nu Ξ σ r f₂ ≠ ⊤) {s : ℝ}
    (hφ : nu Ξ σ s φ ≠ ⊤) :
    Integrable (convolutionIntegrand f₁ f₂ φ) (μ.prod μ) := by
  have hcont : Continuous (convolutionIntegrand f₁ f₂ φ) :=
    ((hc₁.comp continuous_fst).mul (hc₂.comp ((continuous_inv.comp continuous_fst).mul
      continuous_snd))).mul (hφc.comp continuous_snd)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, convolutionIntegrand, enorm_mul]
  rw [lintegral_prod_symm _ (hcont.enorm.measurable.aemeasurable.congr
    (Eventually.of_forall fun z => by simp only [convolutionIntegrand, enorm_mul]))]
  simp only
  simp_rw [lintegral_mul_const' _ _ enorm_ne_top]
  exact hw.lintegral_lintegral_enorm_mul_lt_top h₁ h₂ hφ

/-- Fubini for the convolution: `∫_G (f₁ * f₂)(g) φ(g) dg = ∫_G f₁(h) ∫_G f₂(y) φ(h y) dy dh`
for `f₁, f₂` as in `integrable_prod` and `φ` continuous with `ν_s(φ) < ∞`. -/
theorem integral_convolution_mul (hw : ConvolutionWeights μ K Ξ σ) {f₁ f₂ φ : G → ℂ}
    (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) (hφc : Continuous φ)
    (h₁ : ∀ r, nu Ξ σ r f₁ ≠ ⊤) (h₂ : ∀ r, nu Ξ σ r f₂ ≠ ⊤) {s : ℝ}
    (hφ : nu Ξ σ s φ ≠ ⊤) :
    ∫ g, convolution μ f₁ f₂ g * φ g ∂μ = ∫ h, f₁ h * ∫ y, f₂ y * φ (h * y) ∂μ ∂μ := by
  have hint := hw.integrable_prod hc₁ hc₂ hφc h₁ h₂ hφ
  simp only [convolution_apply]
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (f := fun h g => f₁ h * f₂ (h⁻¹ * g) * φ g) hint]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  simp only
  simp_rw [mul_assoc, ← integral_const_mul]
  rw [← integral_mul_left_eq_self (fun g => f₁ h * (f₂ (h⁻¹ * g) * φ g)) h]
  simp only [inv_mul_cancel_left]

end ConvolutionWeights

end Fubini

section Operator

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] {Ξ σ : G → ℝ}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- Every `f ∈ C(G)` has all seminorms `ν_r(f)` finite. -/
theorem Space.forall_nu_ne_top (f : Space Ξ σ) : ∀ r, nu Ξ σ r f ≠ ⊤ := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  exact fun r => (hK.2 r).ne

omit [BorelSpace G] [SecondCountableTopology G] in
/-- `ℓ(ρ(h) π(f) v) = ∫_G f(y) ℓ(ρ(h y) v) dμ(y)`. -/
theorem eval_rho_schwartzAction [OpensMeasurableSpace G] [MeasurableMul G]
    (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (f : Space Ξ σ) (v : V) (ℓ : SmoothDual ρ) (h : G) :
    ℓ.val (ρ h (schwartzAction hw hρ hT f v)) = ∫ y, f y * ℓ.val (ρ (h * y) v) ∂μ := by
  have h₁ : ℓ.val (ρ h (schwartzAction hw hρ hT f v)) =
      (smoothContragredient ρ h⁻¹ ℓ).val (schwartzAction hw hρ hT f v) := by
    change _ = ℓ.val (ρ h⁻¹⁻¹ _)
    rw [inv_inv]
  rw [h₁, schwartzAction_eval]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change f y * ℓ.val (ρ h⁻¹⁻¹ (ρ y v)) = f y * ℓ.val (ρ (h * y) v)
  rw [inv_inv, map_mul, Module.End.mul_apply]

/-- Waldspurger III.7: `π(f₁ * f₂) = π(f₁) π(f₂)` for `f₁, f₂ ∈ C(G)`. -/
theorem schwartzAction_convolution [SFinite μ] {K : Subgroup G} [CompactSpace K]
    (hw : L2Weights μ Ξ σ) (hc : ConvolutionWeights μ K Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (f₁ f₂ : Space Ξ σ) :
    schwartzAction hw hρ hT (Space.convolution hc f₁ f₂) =
      schwartzAction hw hρ hT f₁ * schwartzAction hw hρ hT f₂ := by
  refine LinearMap.ext fun v => ext_smoothDual hρ.1 fun ℓ => ?_
  rw [Module.End.mul_apply, schwartzAction_eval, schwartzAction_eval]
  simp_rw [eval_rho_schwartzAction hw hρ hT f₂ v ℓ]
  obtain ⟨r, hr⟩ := exists_nu_coefficient_ne_top hw hT v ℓ
  exact hc.integral_convolution_mul (Space.continuous f₁) (Space.continuous f₂)
    (continuous_coefficient hρ.1 v ℓ) (Space.forall_nu_ne_top f₁) (Space.forall_nu_ne_top f₂) hr

omit [BorelSpace G] [SecondCountableTopology G] in
/-- `π(f') = ρ(a) π(f)` for the left translate `f'(x) = f(a⁻¹ x)` of `f`. -/
theorem schwartzAction_translate_left [OpensMeasurableSpace G] [MeasurableMul G]
    (hw : L2Weights μ Ξ σ) (ht : TranslationWeights Ξ σ) (hρ : IsAdmissible ρ)
    (hT : HasTemperedCoefficients Ξ σ ρ) (a : G) (f : Space Ξ σ) :
    schwartzAction hw hρ hT (Space.translate ht 1 a f) = ρ a * schwartzAction hw hρ hT f := by
  refine LinearMap.ext fun v => ext_smoothDual hρ.1 fun ℓ => ?_
  rw [Module.End.mul_apply, schwartzAction_eval, eval_rho_schwartzAction hw hρ hT f v ℓ]
  rw [← integral_mul_left_eq_self (fun x => Space.translate ht 1 a f x * ℓ.val (ρ x v)) a]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Space.translate_apply, mul_one, inv_mul_cancel_left]

omit [BorelSpace G] [SecondCountableTopology G] in
/-- For a right invariant measure, `π(f') = π(f) ρ(a⁻¹)` for the right translate
`f'(x) = f(x a)` of `f`. -/
theorem schwartzAction_translate_right [OpensMeasurableSpace G] [MeasurableMul G]
    [μ.IsMulRightInvariant] (hw : L2Weights μ Ξ σ) (ht : TranslationWeights Ξ σ)
    (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ) (a : G) (f : Space Ξ σ) :
    schwartzAction hw hρ hT (Space.translate ht a 1 f) = schwartzAction hw hρ hT f * ρ a⁻¹ := by
  refine LinearMap.ext fun v => ext_smoothDual hρ.1 fun ℓ => ?_
  rw [Module.End.mul_apply, schwartzAction_eval, schwartzAction_eval]
  rw [← integral_mul_right_eq_self (fun x => Space.translate ht a 1 f x * ℓ.val (ρ x v)) a⁻¹]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Space.translate_apply, inv_one, one_mul, inv_mul_cancel_right, map_mul,
    Module.End.mul_apply]

end Operator

end Langlands.HarishChandraSchwartz

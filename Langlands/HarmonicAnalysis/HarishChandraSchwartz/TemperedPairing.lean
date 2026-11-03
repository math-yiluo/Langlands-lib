import Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2

/-! # Functions of tempered growth and their pairing with `C(G)`

Waldspurger 2003, III.2: `C^w_lisse(G)` is the space of smooth functions `φ` with
`|φ(g)| ≤ c Ξ(g) (1 + σ(g))^r` for some `c` and `r`; a representation is tempered when its
coefficients lie in it. For such `φ` and `f ∈ C(G)` the integral `∫_G f(g) φ(g) dg`
converges absolutely, by Lemma II.1.5, and depends continuously on `f`; this is the
convergence used for `π(f)` in III.7 and for the pairings of VII.1. This module proves it
for arbitrary weights satisfying `L2Weights` (which contains Lemma II.1.5).
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

universe u

section Growth

variable {G : Type u} {Ξ σ : G → ℝ}

/-- Tempered growth (Waldspurger III.2): there are `c` and `r` with
`|φ(g)| ≤ c Ξ(g) (1 + σ(g))^r` for all `g`. -/
def HasTemperedGrowth (Ξ σ : G → ℝ) (φ : G → ℂ) : Prop :=
  ∃ c r : ℝ, ∀ g, ‖φ g‖ ≤ c * Ξ g * (1 + σ g) ^ r

/-- Tempered growth is the finiteness of one seminorm `ν_s` (with `s = -r`). -/
theorem hasTemperedGrowth_iff (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (φ : G → ℂ) :
    HasTemperedGrowth Ξ σ φ ↔ ∃ s : ℝ, nu Ξ σ s φ ≠ ⊤ := by
  constructor
  · rintro ⟨c, r, h⟩
    refine ⟨-r, ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := c)) (iSup_le fun g => ?_)⟩
    have hb : 0 < 1 + σ g := by linarith [hσ g]
    rw [weight, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : 0 ≤ (Ξ g)⁻¹ * (1 + σ g) ^ (-r) :=
      mul_nonneg (inv_nonneg.mpr (hΞ g).le) (Real.rpow_nonneg hb.le _)
    calc ‖φ g‖ * ((Ξ g)⁻¹ * (1 + σ g) ^ (-r))
        ≤ c * Ξ g * (1 + σ g) ^ r * ((Ξ g)⁻¹ * (1 + σ g) ^ (-r)) :=
          mul_le_mul_of_nonneg_right (h g) hw
      _ = c * (Ξ g * (Ξ g)⁻¹) * ((1 + σ g) ^ r * (1 + σ g) ^ (-r)) := by ring
      _ = c := by
          rw [mul_inv_cancel₀ (hΞ g).ne', ← Real.rpow_add hb, add_neg_cancel, Real.rpow_zero]
          ring
  · rintro ⟨s, hs⟩
    exact ⟨(nu Ξ σ s φ).toReal, -s, fun g => by
      have := norm_le_of_nu hΞ hσ hs g
      linarith⟩

theorem HasTemperedGrowth.add (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) {φ₁ φ₂ : G → ℂ}
    (h₁ : HasTemperedGrowth Ξ σ φ₁) (h₂ : HasTemperedGrowth Ξ σ φ₂) :
    HasTemperedGrowth Ξ σ (φ₁ + φ₂) := by
  rw [hasTemperedGrowth_iff hΞ hσ] at h₁ h₂ ⊢
  obtain ⟨s₁, h₁⟩ := h₁
  obtain ⟨s₂, h₂⟩ := h₂
  refine ⟨min s₁ s₂, ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨h₁, h₂⟩) ?_⟩
  exact (nu_add_le _ _).trans (add_le_add (nu_mono hσ (min_le_left _ _) _)
    (nu_mono hσ (min_le_right _ _) _))

theorem HasTemperedGrowth.smul {φ : G → ℂ} (h : HasTemperedGrowth Ξ σ φ) (c : ℂ) :
    HasTemperedGrowth Ξ σ (c • φ) := by
  obtain ⟨C, r, h⟩ := h
  refine ⟨‖c‖ * C, r, fun g => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((h g).trans_eq (by ring)) (norm_nonneg _)

/-- Waldspurger's `C^w_lisse(G)` (III.2): `φ` is bi-invariant under some compact open
subgroup and has tempered growth. -/
def IsTemperedSmooth [Group G] [TopologicalSpace G] (Ξ σ : G → ℝ) (φ : G → ℂ) : Prop :=
  (∃ H : CompactOpenSubgroup G, IsBiInvariant H.toSubgroup φ) ∧ HasTemperedGrowth Ξ σ φ

theorem IsTemperedSmooth.continuous [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℂ} (h : IsTemperedSmooth Ξ σ φ) : Continuous φ := by
  obtain ⟨⟨H, hH⟩, -⟩ := h
  exact (IsBiInvariant.isLocallyConstant (K := H) hH).continuous

end Growth

section Pairing

variable {G : Type u} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G]
  {μ : Measure G} {Ξ σ : G → ℝ}

namespace L2Weights

omit [TopologicalSpace G] [OpensMeasurableSpace G] in
/-- `∫_G |f| |φ| dμ ≤ ν_{d+r}(f) ν_{-r}(φ) c`, where `d` and `c` are the exponent and the
constant of Lemma II.1.5 in `L2Weights`. -/
theorem lintegral_enorm_mul_le_of_nu (hw : L2Weights μ Ξ σ) (r : ℝ) {f φ : G → ℂ}
    (hf : nu Ξ σ (hw.exponent + r) f ≠ ⊤) (hφ : nu Ξ σ (-r) φ ≠ ⊤) :
    ∫⁻ g, ‖f g‖ₑ * ‖φ g‖ₑ ∂μ ≤ nu Ξ σ (hw.exponent + r) f * nu Ξ σ (-r) φ * hw.const :=
  hw.lintegral_enorm_mul_le (by ring) hf hφ

/-- For `f` continuous with `ν_{d+r}(f) < ∞` and `φ` continuous with `ν_{-r}(φ) < ∞`, the
function `f φ` is integrable. -/
theorem integrable_mul_of_nu (hw : L2Weights μ Ξ σ) (r : ℝ) {f φ : G → ℂ}
    (hfc : Continuous f) (hφc : Continuous φ) (hf : nu Ξ σ (hw.exponent + r) f ≠ ⊤)
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) : Integrable (fun g => f g * φ g) μ := by
  refine ⟨(hfc.mul hφc).aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, enorm_mul]
  exact lt_of_le_of_lt (hw.lintegral_enorm_mul_le_of_nu r hf hφ)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hf.lt_top hφ.lt_top) hw.const_lt_top)

omit [TopologicalSpace G] [OpensMeasurableSpace G] in
/-- `|∫_G f φ dμ| ≤ ν_{d+r}(f) ν_{-r}(φ) c`. -/
theorem enorm_integral_mul_le (hw : L2Weights μ Ξ σ) (r : ℝ) {f φ : G → ℂ}
    (hf : nu Ξ σ (hw.exponent + r) f ≠ ⊤) (hφ : nu Ξ σ (-r) φ ≠ ⊤) :
    ‖∫ g, f g * φ g ∂μ‖ₑ ≤ nu Ξ σ (hw.exponent + r) f * nu Ξ σ (-r) φ * hw.const :=
  (enorm_integral_le_lintegral_enorm _).trans (by
    simp only [enorm_mul]
    exact hw.lintegral_enorm_mul_le_of_nu r hf hφ)

end L2Weights

variable [Group G] [IsTopologicalGroup G]

namespace Level

/-- The functional `f ↦ ∫_G f φ dμ` on a level `C_K`, for `φ` continuous with
`ν_{-r}(φ) < ∞`. -/
def temperedPairing (hw : L2Weights μ Ξ σ) {φ : G → ℂ} (hφc : Continuous φ) {r : ℝ}
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (K : CompactOpenSubgroup G) : Level Ξ σ K →ₗ[ℂ] ℂ where
  toFun f := ∫ g, f g * φ g ∂μ
  map_add' f₁ f₂ := by
    have h₁ : Integrable (fun g => f₁ g * φ g) μ := hw.integrable_mul_of_nu r
      (continuous_of_mem_levelSubmodule (f₁ : levelSubmodule Ξ σ K.toSubgroup).2) hφc
      (nu_ne_top f₁ _) hφ
    have h₂ : Integrable (fun g => f₂ g * φ g) μ := hw.integrable_mul_of_nu r
      (continuous_of_mem_levelSubmodule (f₂ : levelSubmodule Ξ σ K.toSubgroup).2) hφc
      (nu_ne_top f₂ _) hφ
    rw [← integral_add h₁ h₂]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change ((f₁ + f₂ : Level Ξ σ K) : G → ℂ) g * φ g = f₁ g * φ g + f₂ g * φ g
    rw [show ((f₁ + f₂ : Level Ξ σ K) : G → ℂ) g = f₁ g + f₂ g from rfl, add_mul]
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    change ((c • f : Level Ξ σ K) : G → ℂ) g * φ g = c * (f g * φ g)
    rw [show ((c • f : Level Ξ σ K) : G → ℂ) g = c * f g from rfl, mul_assoc]

theorem continuous_temperedPairing (hw : L2Weights μ Ξ σ) {φ : G → ℂ} (hφc : Continuous φ)
    {r : ℝ} (hφ : nu Ξ σ (-r) φ ≠ ⊤) (K : CompactOpenSubgroup G) :
    Continuous (temperedPairing hw hφc hφ K) := by
  refine (withSeminorms K).continuous_of_isBounded (norm_withSeminorms ℂ ℂ) _ ?_
  refine Seminorm.IsBounded.of_real fun _ => ?_
  refine ⟨{hw.exponent + r}, (nu Ξ σ (-r) φ * hw.const).toReal, fun f => ?_⟩
  rw [Finset.sup_singleton]
  change ‖∫ g, f g * φ g ∂μ‖ ≤
    (nu Ξ σ (-r) φ * hw.const).toReal * (nu Ξ σ (hw.exponent + r) f).toReal
  have hfin : nu Ξ σ (-r) φ * hw.const ≠ ⊤ := ENNReal.mul_ne_top hφ hw.const_lt_top.ne
  have hB : nu Ξ σ (hw.exponent + r) f ≠ ⊤ := nu_ne_top f _
  have h := hw.enorm_integral_mul_le r hB hφ
  rw [mul_assoc] at h
  calc ‖∫ g, f g * φ g ∂μ‖ = (‖∫ g, f g * φ g ∂μ‖ₑ).toReal := (toReal_enorm _).symm
    _ ≤ (nu Ξ σ (hw.exponent + r) f * (nu Ξ σ (-r) φ * hw.const)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hB hfin) h
    _ = (nu Ξ σ (-r) φ * hw.const).toReal * (nu Ξ σ (hw.exponent + r) f).toReal := by
        rw [ENNReal.toReal_mul, mul_comm]

end Level

namespace Space

variable [Nonempty (CompactOpenSubgroup G)]

/-- For `f ∈ C(G)` and `φ` continuous with `ν_{-r}(φ) < ∞`, `f φ` is integrable. -/
theorem integrable_mul (hw : L2Weights μ Ξ σ) {φ : G → ℂ} (hφc : Continuous φ) {r : ℝ}
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) (f : Space Ξ σ) : Integrable (fun g => f g * φ g) μ := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f)
  exact hw.integrable_mul_of_nu r (continuous_of_mem_levelSubmodule hK) hφc (hK.2 _).ne hφ

/-- Waldspurger III.2 and III.7: for `φ` continuous of tempered growth (`ν_{-r}(φ) < ∞`),
`f ↦ ∫_G f φ dμ` is a continuous linear functional on `C(G)`. -/
def temperedPairing (hw : L2Weights μ Ξ σ) {φ : G → ℂ} (hφc : Continuous φ) {r : ℝ}
    (hφ : nu Ξ σ (-r) φ ≠ ⊤) : Space Ξ σ →L[ℂ] ℂ :=
  mkCLM
    { toFun := fun f => ∫ g, f g * φ g ∂μ
      map_add' := fun f₁ f₂ => by
        rw [← integral_add (integrable_mul hw hφc hφ f₁) (integrable_mul hw hφc hφ f₂)]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        change ((f₁ + f₂ : Space Ξ σ) : G → ℂ) g * φ g = f₁ g * φ g + f₂ g * φ g
        rw [show ((f₁ + f₂ : Space Ξ σ) : G → ℂ) g = f₁ g + f₂ g from rfl, add_mul]
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun g => ?_)
        change ((c • f : Space Ξ σ) : G → ℂ) g * φ g = c * (f g * φ g)
        rw [show ((c • f : Space Ξ σ) : G → ℂ) g = c * f g from rfl, mul_assoc] }
    fun K => by
      have h := Level.continuous_temperedPairing hw hφc hφ K
      exact h

@[simp] theorem temperedPairing_apply (hw : L2Weights μ Ξ σ) {φ : G → ℂ} (hφc : Continuous φ)
    {r : ℝ} (hφ : nu Ξ σ (-r) φ ≠ ⊤) (f : Space Ξ σ) :
    temperedPairing hw hφc hφ f = ∫ g, f g * φ g ∂μ :=
  rfl

end Space

end Pairing

end Langlands.HarishChandraSchwartz

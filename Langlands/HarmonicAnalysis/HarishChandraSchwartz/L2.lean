import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution
import Mathlib.MeasureTheory.Function.L2Space

/-! # Inversion and the `L²` inner product on the Harish-Chandra Schwartz space

Waldspurger 2003, VII.1: for `f ∈ C(G)` the function `ˇf(g) = f(g⁻¹)` lies in `C(G)`, and
for functions `f₁, f₂` on a measure space `X` with `f̄₁ f₂ ∈ L¹(X)` one writes
`(f₁, f₂)_X = ∫_X f̄₁(x) f₂(x) dx`. For arbitrary weights `Ξ`, `σ` with explicit hypotheses,
this module shows that `f ↦ ˇf` is a continuous linear involution of `C(G)`, and that
`C(G)` embeds continuously and linearly in `L²(G)`, with `L²` inner product `(f₁, f₂)_G`.
-/

noncomputable section

open scoped ENNReal NNReal Topology ComplexConjugate
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

universe u

section Check

variable {G : Type u} [Group G]

/-- The function `ˇf(g) = f(g⁻¹)` (Waldspurger VII.1). -/
def check (f : G → ℂ) : G → ℂ :=
  fun g => f g⁻¹

@[simp] theorem check_apply (f : G → ℂ) (g : G) : check f g = f g⁻¹ :=
  rfl

@[simp] theorem check_check (f : G → ℂ) : check (check f) = f := by
  funext g
  simp

theorem check_add (f₁ f₂ : G → ℂ) : check (f₁ + f₂) = check f₁ + check f₂ :=
  rfl

theorem check_smul (c : ℂ) (f : G → ℂ) : check (c • f) = c • check f :=
  rfl

/-- If `f` is `H`-bi-invariant, so is `ˇf`. -/
theorem IsBiInvariant.check {H : Subgroup G} {f : G → ℂ} (hf : IsBiInvariant H f) :
    IsBiInvariant H (check f) := by
  intro h₁ hh₁ h₂ hh₂ g
  simp only [check_apply, mul_inv_rev]
  rw [← mul_assoc]
  exact hf _ (H.inv_mem hh₂) _ (H.inv_mem hh₁) _

variable {Ξ σ : G → ℝ}

theorem weight_inv (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (r : ℝ) (g : G) :
    weight Ξ σ r g⁻¹ = weight Ξ σ r g := by
  simp only [weight, hΞ, hσ]

/-- `ν_r(ˇf) = ν_r(f)` when `Ξ` and `σ` are invariant under `g ↦ g⁻¹`. -/
theorem nu_check (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (r : ℝ) (f : G → ℂ) :
    nu Ξ σ r (check f) = nu Ξ σ r f := by
  have h := Equiv.iSup_comp (g := fun g => ‖f g‖ₑ * weight Ξ σ r g) (Equiv.inv G)
  simp only [Equiv.inv_apply, weight_inv hΞ hσ] at h
  exact h

theorem check_mem_levelSubmodule (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
    {H : Subgroup G} {f : G → ℂ} (hf : f ∈ levelSubmodule Ξ σ H) :
    check f ∈ levelSubmodule Ξ σ H :=
  ⟨hf.1.check, fun r => by
    rw [nu_check hΞ hσ]
    exact hf.2 r⟩

/-- `f ↦ ˇf` maps `C(G)` into itself (Waldspurger VII.1). -/
theorem check_mem_schwartzSubmodule [TopologicalSpace G] (hΞ : ∀ g, Ξ g⁻¹ = Ξ g)
    (hσ : ∀ g, σ g⁻¹ = σ g) {f : G → ℂ} (hf : f ∈ schwartzSubmodule Ξ σ) :
    check f ∈ schwartzSubmodule Ξ σ := by
  let L : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := check
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle : schwartzSubmodule Ξ σ ≤ (schwartzSubmodule Ξ σ).comap L :=
    iSup_le fun K _ hf' => levelSubmodule_le_schwartzSubmodule Ξ σ K
      (check_mem_levelSubmodule hΞ hσ hf')
  exact hle hf

end Check

section CheckOperators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Ξ σ : G → ℝ}

namespace Level

/-- `f ↦ ˇf` on a level `C_K`. -/
def check (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (K : CompactOpenSubgroup G) :
    Level Ξ σ K →ₗ[ℂ] Level Ξ σ K where
  toFun f := (⟨HarishChandraSchwartz.check f,
    check_mem_levelSubmodule hΞ hσ (f : levelSubmodule Ξ σ K.toSubgroup).2⟩ :
      levelSubmodule Ξ σ K.toSubgroup)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] in
@[simp] theorem coe_check (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
    (K : CompactOpenSubgroup G) (f : Level Ξ σ K) :
    ((check hΞ hσ K f : Level Ξ σ K) : G → ℂ) = HarishChandraSchwartz.check f :=
  rfl

omit [IsTopologicalGroup G] in
theorem continuous_check (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
    (K : CompactOpenSubgroup G) : Continuous (check hΞ hσ K) :=
  continuous_of_nu_le _ fun r => ⟨r, 1, ENNReal.one_ne_top, fun f => by
    rw [one_mul]
    exact (nu_check hΞ hσ r f).le⟩

end Level

namespace Space

/-- `f ↦ ˇf` on `C(G)`, as a linear map. -/
def checkLinear (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) :
    Space Ξ σ →ₗ[ℂ] Space Ξ σ where
  toFun f := (⟨HarishChandraSchwartz.check f, check_mem_schwartzSubmodule hΞ hσ (coe_mem f)⟩ :
    schwartzSubmodule Ξ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `f ↦ ˇf` is a continuous linear map `C(G) → C(G)`; it is built from III.6(1). -/
def check (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) : Space Ξ σ →L[ℂ] Space Ξ σ :=
  mkCLM (checkLinear hΞ hσ) fun K => by
    have h : (checkLinear hΞ hσ ∘ ofLevel K : Level Ξ σ K → Space Ξ σ) =
        ofLevel K ∘ Level.check hΞ hσ K :=
      funext fun _ => ext fun _ => rfl
    rw [h]
    exact (continuous_ofLevel _).comp (Level.continuous_check hΞ hσ K)

omit [IsTopologicalGroup G] in
@[simp] theorem coe_check (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (f : Space Ξ σ) :
    ((check hΞ hσ f : Space Ξ σ) : G → ℂ) = HarishChandraSchwartz.check f :=
  rfl

omit [IsTopologicalGroup G] in
@[simp] theorem check_check (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (f : Space Ξ σ) :
    check hΞ hσ (check hΞ hσ f) = f :=
  ext fun g => congrFun (HarishChandraSchwartz.check_check (f : G → ℂ)) g

end Space

end CheckOperators

section Pointwise

variable {G : Type u} {Ξ σ : G → ℝ}

/-- `|f₁(g)| |f₂(g)| ≤ ν_{r₁}(f₁) ν_{r₂}(f₂) Ξ(g)² (1 + σ(g))^{-(r₁ + r₂)}`. -/
theorem enorm_mul_enorm_le (hΞ : ∀ g, 0 < Ξ g) (hσ : ∀ g, 0 ≤ σ g) (r₁ r₂ : ℝ)
    (f₁ f₂ : G → ℂ) (g : G) :
    ‖f₁ g‖ₑ * ‖f₂ g‖ₑ ≤
      nu Ξ σ r₁ f₁ * nu Ξ σ r₂ f₂ * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(r₁ + r₂))) := by
  have hb : 0 < 1 + σ g := by linarith [hσ g]
  have hA : 0 ≤ Ξ g * (1 + σ g) ^ (-r₁) := mul_nonneg (hΞ g).le (Real.rpow_nonneg hb.le _)
  calc ‖f₁ g‖ₑ * ‖f₂ g‖ₑ
      ≤ (nu Ξ σ r₁ f₁ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r₁))) *
          (nu Ξ σ r₂ f₂ * ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r₂))) :=
        mul_le_mul' (enorm_le_nu_mul hΞ hσ f₁ r₁ g) (enorm_le_nu_mul hΞ hσ f₂ r₂ g)
    _ = nu Ξ σ r₁ f₁ * nu Ξ σ r₂ f₂ *
          ENNReal.ofReal (Ξ g * (1 + σ g) ^ (-r₁) * (Ξ g * (1 + σ g) ^ (-r₂))) := by
        rw [ENNReal.ofReal_mul hA]
        ring
    _ = nu Ξ σ r₁ f₁ * nu Ξ σ r₂ f₂ * ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(r₁ + r₂))) := by
        rw [neg_add, Real.rpow_add hb]
        ring_nf

end Pointwise

section Pairing

variable {G : Type u} [MeasurableSpace G]

/-- `(f₁, f₂)_G = ∫_G conj(f₁(g)) f₂(g) dμ(g)` (Waldspurger VII.1). It is a Bochner integral,
so it is `0` when the integrand is not integrable. -/
def pairing (μ : Measure G) (f₁ f₂ : G → ℂ) : ℂ :=
  ∫ g, conj (f₁ g) * f₂ g ∂μ

theorem pairing_apply (μ : Measure G) (f₁ f₂ : G → ℂ) :
    pairing μ f₁ f₂ = ∫ g, conj (f₁ g) * f₂ g ∂μ :=
  rfl

/-- The hypotheses on the weights used for the `L²` theory of `C(G)`: `Ξ > 0`, `σ ≥ 0`, and
`∫_G Ξ(g)² (1 + σ(g))^{-d} dμ(g) < ∞` for some real `d` (Lemma II.1.5 of Waldspurger, where
`d ∈ ℕ`). -/
structure L2Weights (μ : Measure G) (Ξ σ : G → ℝ) : Prop where
  pos : ∀ g, 0 < Ξ g
  nonneg : ∀ g, 0 ≤ σ g
  square : ∃ d : ℝ, ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-d)) ∂μ < ⊤

namespace L2Weights

variable {μ : Measure G} {Ξ σ : G → ℝ}

/-- The exponent `d` chosen from `L2Weights.square`. -/
def exponent (hw : L2Weights μ Ξ σ) : ℝ :=
  hw.square.choose

/-- The constant `∫_G Ξ(g)² (1 + σ(g))^{-d} dμ(g)` for `d = exponent`. -/
def const (hw : L2Weights μ Ξ σ) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-hw.exponent)) ∂μ

theorem const_lt_top (hw : L2Weights μ Ξ σ) : hw.const < ⊤ :=
  hw.square.choose_spec

/-- `∫_G |f₁| |f₂| dμ ≤ ν_{r₁}(f₁) ν_{r₂}(f₂) c` for `r₁ + r₂ = d`. -/
theorem lintegral_enorm_mul_le (hw : L2Weights μ Ξ σ) {r₁ r₂ : ℝ}
    (hr : r₁ + r₂ = hw.exponent) {f₁ f₂ : G → ℂ} (h₁ : nu Ξ σ r₁ f₁ ≠ ⊤)
    (h₂ : nu Ξ σ r₂ f₂ ≠ ⊤) :
    ∫⁻ g, ‖f₁ g‖ₑ * ‖f₂ g‖ₑ ∂μ ≤ nu Ξ σ r₁ f₁ * nu Ξ σ r₂ f₂ * hw.const := by
  rw [const, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top h₁ h₂)]
  refine lintegral_mono fun g => ?_
  have h := enorm_mul_enorm_le hw.pos hw.nonneg r₁ r₂ f₁ f₂ g
  rwa [hr] at h

variable [TopologicalSpace G] [OpensMeasurableSpace G]

/-- For continuous `f₁`, `f₂` with `ν_{r₁}(f₁), ν_{r₂}(f₂) < ∞` and `r₁ + r₂ = d`, the
function `conj(f₁) f₂` is integrable. -/
theorem integrable_conj_mul (hw : L2Weights μ Ξ σ) {f₁ f₂ : G → ℂ} (hc₁ : Continuous f₁)
    (hc₂ : Continuous f₂) {r₁ r₂ : ℝ} (hr : r₁ + r₂ = hw.exponent) (h₁ : nu Ξ σ r₁ f₁ ≠ ⊤)
    (h₂ : nu Ξ σ r₂ f₂ ≠ ⊤) :
    Integrable (fun g => conj (f₁ g) * f₂ g) μ := by
  refine ⟨((Complex.continuous_conj.comp hc₁).mul hc₂).aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, enorm_mul, RCLike.enorm_conj]
  exact lt_of_le_of_lt (hw.lintegral_enorm_mul_le hr h₁ h₂)
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top h₁.lt_top h₂.lt_top) hw.const_lt_top)

/-- A continuous `f` with `ν_{d/2}(f) < ∞` is square integrable. -/
theorem memLp_two (hw : L2Weights μ Ξ σ) {f : G → ℂ} (hc : Continuous f)
    (hf : nu Ξ σ (hw.exponent / 2) f ≠ ⊤) : MemLp f 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr ?_
  refine (hw.integrable_conj_mul hc hc (add_halves _) hf hf).norm.congr
    (Eventually.of_forall fun g => ?_)
  simp only [norm_mul, RCLike.norm_conj, sq]

/-- `‖f‖_{L²} ≤ ν_{d/2}(f) c^{1/2}`. -/
theorem eLpNorm_le (hw : L2Weights μ Ξ σ) {f : G → ℂ} (hc : Continuous f)
    (hf : nu Ξ σ (hw.exponent / 2) f ≠ ⊤) :
    eLpNorm f 2 μ ≤ nu Ξ σ (hw.exponent / 2) f * hw.const ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hc.aestronglyMeasurable]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hle : ∫⁻ g, ‖f g‖ₑ ^ (2 : ℝ) ∂μ ≤
      nu Ξ σ (hw.exponent / 2) f ^ (2 : ℝ) * hw.const := by
    have h := hw.lintegral_enorm_mul_le (add_halves hw.exponent) hf hf
    simp only [ENNReal.rpow_two, sq]
    exact h
  calc (∫⁻ g, ‖f g‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
      ≤ (nu Ξ σ (hw.exponent / 2) f ^ (2 : ℝ) * hw.const) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hle (by norm_num)
    _ = nu Ξ σ (hw.exponent / 2) f * hw.const ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.rpow_mul]
        norm_num

end L2Weights

end Pairing

section ConvolutionWeights

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} {K : Subgroup G} [CompactSpace K]
  {Ξ σ : G → ℝ}

/-- The hypotheses of Lemma III.6.1 contain those of the `L²` theory. -/
theorem ConvolutionWeights.toL2Weights (hw : ConvolutionWeights μ K Ξ σ) :
    L2Weights μ Ξ σ :=
  ⟨hw.pos, hw.nonneg, ⟨hw.squareExponent, hw.lintegral_square_lt_top⟩⟩

end ConvolutionWeights

section L2Operators

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] {μ : Measure G} {Ξ σ : G → ℝ}

namespace Level

theorem memLp_two (hw : L2Weights μ Ξ σ) {K : CompactOpenSubgroup G} (f : Level Ξ σ K) :
    MemLp (f : G → ℂ) 2 μ :=
  hw.memLp_two (continuous_of_mem_levelSubmodule (f : levelSubmodule Ξ σ K.toSubgroup).2)
    (nu_ne_top f _)

/-- The inclusion `C_K → L²(G)`. -/
def toL2 (hw : L2Weights μ Ξ σ) (K : CompactOpenSubgroup G) :
    Level Ξ σ K →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_two hw f).toLp f
  map_add' f₁ f₂ := MemLp.toLp_add (memLp_two hw f₁) (memLp_two hw f₂)
  map_smul' c f := MemLp.toLp_const_smul c (memLp_two hw f)

theorem continuous_toL2 (hw : L2Weights μ Ξ σ) (K : CompactOpenSubgroup G) :
    Continuous (toL2 hw K) := by
  refine (withSeminorms K).continuous_of_isBounded (norm_withSeminorms ℂ (Lp ℂ 2 μ)) _ ?_
  refine Seminorm.IsBounded.of_real fun _ => ?_
  refine ⟨{hw.exponent / 2}, (hw.const ^ (1 / 2 : ℝ)).toReal, fun f => ?_⟩
  rw [Finset.sup_singleton]
  change ‖(memLp_two hw f).toLp f‖ ≤
    (hw.const ^ (1 / 2 : ℝ)).toReal * (nu Ξ σ (hw.exponent / 2) f).toReal
  have hC : hw.const ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hw.const_lt_top.ne
  rw [Lp.norm_toLp, mul_comm, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (nu_ne_top f _) hC)
    (hw.eLpNorm_le (continuous_of_mem_levelSubmodule (f : levelSubmodule Ξ σ K.toSubgroup).2)
      (nu_ne_top f _))

end Level

namespace Space

variable [Nonempty (CompactOpenSubgroup G)]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- Every element of `C(G)` is continuous. -/
theorem continuous (f : Space Ξ σ) : Continuous (f : G → ℂ) := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f)
  exact continuous_of_mem_levelSubmodule hK

/-- `C(G) ⊆ L²(G)`. -/
theorem memLp_two (hw : L2Weights μ Ξ σ) (f : Space Ξ σ) : MemLp (f : G → ℂ) 2 μ := by
  obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f)
  exact hw.memLp_two (continuous_of_mem_levelSubmodule hK) (hK.2 _).ne

/-- For `f₁, f₂ ∈ C(G)` the function `conj(f₁) f₂` is integrable. -/
theorem integrable_conj_mul (hw : L2Weights μ Ξ σ) (f₁ f₂ : Space Ξ σ) :
    Integrable (fun g => conj (f₁ g) * f₂ g) μ := by
  obtain ⟨K₁, h₁⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f₁)
  obtain ⟨K₂, h₂⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (coe_mem f₂)
  exact hw.integrable_conj_mul (continuous_of_mem_levelSubmodule h₁)
    (continuous_of_mem_levelSubmodule h₂) (add_halves _) (h₁.2 _).ne (h₂.2 _).ne

/-- The inclusion `C(G) → L²(G)`, as a linear map. -/
def toL2Linear (hw : L2Weights μ Ξ σ) : Space Ξ σ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_two hw f).toLp f
  map_add' f₁ f₂ := MemLp.toLp_add (memLp_two hw f₁) (memLp_two hw f₂)
  map_smul' c f := MemLp.toLp_const_smul c (memLp_two hw f)

/-- The continuous inclusion `C(G) → L²(G)`; it is built from III.6(1). -/
def toL2 (hw : L2Weights μ Ξ σ) : Space Ξ σ →L[ℂ] Lp ℂ 2 μ :=
  mkCLM (toL2Linear hw) fun K => by
    have h : (toL2Linear hw ∘ ofLevel K : Level Ξ σ K → Lp ℂ 2 μ) = Level.toL2 hw K :=
      funext fun _ => rfl
    rw [h]
    exact Level.continuous_toL2 hw K

theorem coeFn_toL2 (hw : L2Weights μ Ξ σ) (f : Space Ξ σ) :
    (toL2 hw f : G → ℂ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp (memLp_two hw f)

/-- The `L²` inner product of two elements of `C(G)` is `(f₁, f₂)_G`. -/
theorem inner_toL2 (hw : L2Weights μ Ξ σ) (f₁ f₂ : Space Ξ σ) :
    inner ℂ (toL2 hw f₁) (toL2 hw f₂) = pairing μ f₁ f₂ := by
  rw [L2.inner_def, pairing_apply]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 hw f₁, coeFn_toL2 hw f₂] with g h₁ h₂
  rw [h₁, h₂, RCLike.inner_apply']

/-- `(f₂, f₁)_G = conj (f₁, f₂)_G`. -/
theorem pairing_swap (hw : L2Weights μ Ξ σ) (f₁ f₂ : Space Ξ σ) :
    pairing μ f₂ f₁ = conj (pairing μ f₁ f₂) := by
  rw [← inner_toL2 hw, ← inner_toL2 hw, inner_conj_symm]

/-- `(f, f)_G = ‖f‖²_{L²}`. -/
theorem pairing_self (hw : L2Weights μ Ξ σ) (f : Space Ξ σ) :
    pairing μ f f = ((‖toL2 hw f‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_toL2 hw, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The pairing `(f₁, f₂) ↦ (f₁, f₂)_G` is jointly continuous on `C(G) × C(G)`. -/
theorem continuous_pairing (hw : L2Weights μ Ξ σ) :
    Continuous fun p : Space Ξ σ × Space Ξ σ => pairing μ p.1 p.2 := by
  have h : (fun p : Space Ξ σ × Space Ξ σ => pairing μ p.1 p.2) =
      fun p => inner ℂ (toL2 hw p.1) (toL2 hw p.2) :=
    funext fun p => (inner_toL2 hw p.1 p.2).symm
  rw [h]
  exact ((toL2 hw).continuous.comp continuous_fst).inner ((toL2 hw).continuous.comp continuous_snd)

variable [μ.IsOpenPosMeasure]

/-- For a measure that is positive on nonempty open sets, `C(G) → L²(G)` is injective. -/
theorem toL2_injective (hw : L2Weights μ Ξ σ) : Function.Injective (toL2 hw) := by
  intro f₁ f₂ h
  have hae : (f₁ : G → ℂ) =ᵐ[μ] f₂ :=
    (MemLp.toLp_eq_toLp_iff (memLp_two hw f₁) (memLp_two hw f₂)).mp h
  exact DFunLike.coe_injective ((Continuous.ae_eq_iff_eq μ (continuous f₁) (continuous f₂)).mp hae)

/-- For a measure that is positive on nonempty open sets, `(f, f)_G = 0` only for `f = 0`. -/
theorem pairing_self_eq_zero (hw : L2Weights μ Ξ σ) {f : Space Ξ σ} :
    pairing μ f f = 0 ↔ f = 0 := by
  rw [← inner_toL2 hw, inner_self_eq_zero, ← map_zero (toL2 hw)]
  exact (toL2_injective hw).eq_iff

end Space

end L2Operators

end Langlands.HarishChandraSchwartz

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex
import Langlands.Global.Hecke.ConeMellin

/-!
# Measure theory on the mixed space: multiplication, inversion and unfolding over units

Let `V = mixedSpace K` be the mixed space `ℝ^{r₁} × ℂ^{r₂}` of a number field `K`, with its
componentwise ring structure, Lebesgue measure `volume` and norm `N = mixedEmbedding.norm`.
This module collects the measure-theoretic facts about `V` used in the Tate–Hecke proof of the
global functional equation of Hecke `L`-functions:

* change of variables under multiplication, `∫ f (y * x) = N(y)⁻¹ • ∫ f`
  (`integral_comp_mul_left`, `lintegral_comp_mul_left`), from `|det (x ↦ y * x)| = N(y)`
  (`abs_det_mulL`);
* change of variables under componentwise inversion, `∫ N(x)⁻² • g (x⁻¹) = ∫ g`
  (`integral_comp_inv`);
* unfolding over the units: the translates `u • C` (`u ∈ (𝓞 K)ˣ`) of Mathlib's fundamental cone
  `C = fundamentalCone K` cover almost every point exactly `torsionOrder K` times
  (`tsum_indicator_unit_smul`), so that `∑_u ∫_C Ψ (u • x) = torsionOrder K • ∫ Ψ`
  (`tsum_setLIntegral_unit_smul`, `hasSum_setIntegral_unit_smul`);
* the fundamental cone as a `DyadicCone` (`fundamentalDyadicCone`) and the comparison
  `normAtPlace w x ≍ N(x) ^ (1 / [K : ℚ])` on it (`exists_normAtPlace_bounds`).
-/

open MeasureTheory Set Filter Module
open scoped Topology ENNReal Classical

noncomputable section

namespace Langlands.Global.Hecke

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => mixedSpace K

/-! ### Multiplication by an element of the mixed space -/

/-- Multiplication by `y` as a continuous `ℝ`-linear map of the mixed space. -/
def mulL (y : V) : V →L[ℝ] V := ContinuousLinearMap.mul ℝ V y

@[simp] lemma mulL_apply (y x : V) : mulL y x = y * x := rfl

lemma mulL_toLinearMap (y : V) :
    (mulL y : V →ₗ[ℝ] V) = LinearMap.prodMap
      (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (y.1 w)).comp (LinearMap.proj w))
      (LinearMap.pi fun w => (LinearMap.mulLeft ℝ (y.2 w)).comp (LinearMap.proj w)) := by
  ext x <;> simp

lemma det_mulL (y : V) :
    (mulL y).det = (∏ w, y.1 w) * ∏ w, Complex.normSq (y.2 w) := by
  rw [ContinuousLinearMap.det, mulL_toLinearMap, LinearMap.det_prodMap, LinearMap.det_pi,
    LinearMap.det_pi]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl

lemma abs_det_mulL (y : V) : |(mulL y).det| = mixedEmbedding.norm y := by
  classical
  rw [det_mulL, abs_mul, Finset.abs_prod, Finset.abs_prod, mixedEmbedding.norm_apply,
    ← Fintype.prod_subtype_mul_prod_subtype (fun w => IsReal w)]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [normAtPlace_apply_of_isReal w.2, mult_isReal, pow_one, Real.norm_eq_abs]
  · rw [← (Equiv.subtypeEquivRight (fun w => not_isReal_iff_isComplex (w := w))).symm.prod_comp]
    refine Finset.prod_congr rfl fun w _ => ?_
    simp only [Equiv.subtypeEquivRight_symm_apply_coe]
    rw [normAtPlace_apply_of_isComplex w.2, mult_isComplex,
      Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]


/-! ### Componentwise inversion -/

omit [NumberField K] in
lemma normAtPlace_inv (w : InfinitePlace K) (x : V) :
    normAtPlace w x⁻¹ = (normAtPlace w x)⁻¹ := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw, normAtPlace_apply_of_isReal hw, Prod.fst_inv,
      Pi.inv_apply, norm_inv]
  · rw [normAtPlace_apply_of_isComplex hw, normAtPlace_apply_of_isComplex hw, Prod.snd_inv,
      Pi.inv_apply, norm_inv]

lemma norm_inv' (x : V) : mixedEmbedding.norm x⁻¹ = (mixedEmbedding.norm x)⁻¹ := by
  simp only [mixedEmbedding.norm_apply, normAtPlace_inv, inv_pow, Finset.prod_inv_distrib]

lemma norm_neg' (x : V) : mixedEmbedding.norm (-x) = mixedEmbedding.norm x :=
  norm_eq_of_normAtPlace_eq fun w => normAtPlace_neg w x

lemma mul_inv_cancel_of_norm_ne_zero {x : V} (hx : mixedEmbedding.norm x ≠ 0) :
    x * x⁻¹ = 1 := by
  have h := mixedEmbedding.norm_ne_zero_iff.mp hx
  ext w
  · have : x.1 w ≠ 0 := by
      have := h w.1
      rwa [normAtPlace_apply_of_isReal w.2, norm_ne_zero_iff] at this
    simp [this]
  · have : x.2 w ≠ 0 := by
      have := h w.1
      rwa [normAtPlace_apply_of_isComplex w.2, norm_ne_zero_iff] at this
    simp [this]

/-- A point of nonzero norm, as a unit of the mixed space. -/
def unitOfNormNeZero {x : V} (hx : mixedEmbedding.norm x ≠ 0) : Vˣ :=
  ⟨x, x⁻¹, mul_inv_cancel_of_norm_ne_zero hx, by
    rw [mul_comm]; exact mul_inv_cancel_of_norm_ne_zero hx⟩

lemma isOpen_setOf_norm_ne_zero : IsOpen {x : V | mixedEmbedding.norm x ≠ 0} :=
  isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const

lemma measurableSet_setOf_norm_ne_zero : MeasurableSet {x : V | mixedEmbedding.norm x ≠ 0} :=
  isOpen_setOf_norm_ne_zero.measurableSet

lemma hasFDerivAt_inv' {x : V} (hx : mixedEmbedding.norm x ≠ 0) :
    HasFDerivAt (fun y : V => y⁻¹) (mulL (-(x⁻¹ * x⁻¹))) x := by
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) (unitOfNormNeZero hx)
  have h2 : (fun y : V => y⁻¹) =ᶠ[𝓝 x] Ring.inverse := by
    filter_upwards [isOpen_setOf_norm_ne_zero.mem_nhds hx] with y hy
    have := Ring.inverse_unit (unitOfNormNeZero (x := y) hy)
    exact this.symm
  have h3 : -ContinuousLinearMap.mulLeftRight ℝ V ↑(unitOfNormNeZero hx)⁻¹
      ↑(unitOfNormNeZero hx)⁻¹ = mulL (-(x⁻¹ * x⁻¹)) := by
    refine ContinuousLinearMap.ext fun h => ?_
    simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, mulL_apply]
    change -(x⁻¹ * h * x⁻¹) = -(x⁻¹ * x⁻¹) * h
    ring
  rw [← h3]
  exact h1.congr_of_eventuallyEq h2

/-! ### Change of variables -/

lemma det_mulL_ne_zero {y : V} (hy : mixedEmbedding.norm y ≠ 0) : (mulL y).det ≠ 0 := by
  rw [← abs_ne_zero, abs_det_mulL]
  exact hy

lemma map_mulL_volume {y : V} (hy : mixedEmbedding.norm y ≠ 0) :
    Measure.map (mulL y) volume = ENNReal.ofReal (mixedEmbedding.norm y)⁻¹ • volume := by
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure V)
    (f := (mulL y : V →ₗ[ℝ] V)) (det_mulL_ne_zero hy)
  rw [abs_inv, abs_det_mulL] at this
  exact this

/-- Multiplication by a point of nonzero norm, as a homeomorphism. -/
def mulHomeomorph {y : V} (hy : mixedEmbedding.norm y ≠ 0) : V ≃ₜ V where
  toFun x := y * x
  invFun x := y⁻¹ * x
  left_inv x := by
    simp only [← mul_assoc, mul_comm y⁻¹ y, mul_inv_cancel_of_norm_ne_zero hy, one_mul]
  right_inv x := by
    simp only [← mul_assoc, mul_inv_cancel_of_norm_ne_zero hy, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

lemma map_mulHomeomorph_volume {y : V} (hy : mixedEmbedding.norm y ≠ 0) :
    Measure.map (mulHomeomorph hy).toMeasurableEquiv volume =
      ENNReal.ofReal (mixedEmbedding.norm y)⁻¹ • volume := by
  rw [← map_mulL_volume hy]
  rfl

theorem integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : V} (hy : mixedEmbedding.norm y ≠ 0) (f : V → E) :
    ∫ x, f (y * x) = (mixedEmbedding.norm y)⁻¹ • ∫ x, f x := by
  have := MeasureTheory.integral_map_equiv (μ := volume) (mulHomeomorph hy).toMeasurableEquiv f
  rw [map_mulHomeomorph_volume hy, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mixedEmbedding.norm_nonneg y))] at this
  exact this.symm

theorem lintegral_comp_mul_left {y : V} (hy : mixedEmbedding.norm y ≠ 0) (f : V → ℝ≥0∞) :
    ∫⁻ x, f (y * x) = ENNReal.ofReal (mixedEmbedding.norm y)⁻¹ * ∫⁻ x, f x := by
  have := MeasureTheory.lintegral_map_equiv (μ := volume) f (mulHomeomorph hy).toMeasurableEquiv
  rw [map_mulHomeomorph_volume hy, lintegral_smul_measure] at this
  exact this.symm

lemma volume_setOf_norm_eq_zero : volume {x : V | mixedEmbedding.norm x = 0} = 0 := by
  have : {x : V | mixedEmbedding.norm x = 0} = ⋃ w, {x : V | normAtPlace w x = 0} := by
    ext x
    simp [mixedEmbedding.norm_eq_zero_iff]
  rw [this, measure_iUnion_null_iff]
  intro w
  obtain hw | hw := isReal_or_isComplex w
  · have : {x : V | normAtPlace w x = 0} = {x : V | x.1 ⟨w, hw⟩ = 0} := by
      ext x
      simp [normAtPlace_apply_of_isReal hw]
    rw [this]
    exact mixedEmbedding.volume_eq_zero ⟨w, hw⟩
  · let f : V →ₗ[ℝ] ℂ := (LinearMap.proj (R := ℝ) (φ := fun _ => ℂ) ⟨w, hw⟩).comp
      (LinearMap.snd ℝ _ _)
    have : {x : V | normAtPlace w x = 0} = (LinearMap.ker f : Set V) := by
      ext x
      simp [f, normAtPlace_apply_of_isComplex hw]
    rw [this]
    refine Measure.addHaar_submodule _ _ fun h => ?_
    have : ((0, fun _ => 1) : V) ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simp [f] at this

lemma ae_norm_ne_zero : ∀ᵐ x : V, mixedEmbedding.norm x ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.mp volume_setOf_norm_eq_zero

lemma setOf_norm_ne_zero_ae_eq_univ :
    {x : V | mixedEmbedding.norm x ≠ 0} =ᵐ[volume] (univ : Set V) := by
  rw [ae_eq_univ]
  have : {x : V | mixedEmbedding.norm x ≠ 0}ᶜ = {x : V | mixedEmbedding.norm x = 0} := by
    ext x
    simp
  rw [this]
  exact volume_setOf_norm_eq_zero

/-- Change of variables under the componentwise inversion `x ↦ x⁻¹` of the mixed space, whose
Jacobian has absolute value `N(x)⁻²`. -/
theorem integral_comp_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V → E) :
    ∫ x, (mixedEmbedding.norm x)⁻¹ ^ 2 • g x⁻¹ = ∫ x, g x := by
  set U := {x : V | mixedEmbedding.norm x ≠ 0}
  have himage : (fun y : V => y⁻¹) '' U = U := by
    ext x
    simp only [mem_image, mem_ofPred_eq, U]
    refine ⟨?_, fun hx => ⟨x⁻¹, by rw [norm_inv']; exact inv_ne_zero hx, inv_inv x⟩⟩
    rintro ⟨y, hy, rfl⟩
    rw [norm_inv']
    exact inv_ne_zero hy
  have hinj : InjOn (fun y : V => y⁻¹) U := fun a _ b _ h => inv_injective h
  have := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_setOf_norm_ne_zero
    (f := fun y : V => y⁻¹) (f' := fun x => mulL (-(x⁻¹ * x⁻¹)))
    (fun x hx => (hasFDerivAt_inv' hx).hasFDerivWithinAt) hinj g
  rw [himage] at this
  have hR : ∫ x, g x = ∫ x in U, g x := by
    rw [setIntegral_congr_set setOf_norm_ne_zero_ae_eq_univ, setIntegral_univ]
  have hL : ∫ x, (mixedEmbedding.norm x)⁻¹ ^ 2 • g x⁻¹ =
      ∫ x in U, (mixedEmbedding.norm x)⁻¹ ^ 2 • g x⁻¹ := by
    rw [setIntegral_congr_set setOf_norm_ne_zero_ae_eq_univ, setIntegral_univ]
  rw [hR, this, hL]
  refine setIntegral_congr_fun measurableSet_setOf_norm_ne_zero fun x _ => ?_
  rw [abs_det_mulL, norm_neg', map_mul, norm_inv', sq]

/-! ### The action of units -/

omit [NumberField K] in
lemma unit_smul_eq_mul (u : (𝓞 K)ˣ) (x : V) : u • x = mixedEmbedding K (u : K) * x := rfl

lemma norm_mixedEmbedding_unit_ne_zero (u : (𝓞 K)ˣ) :
    mixedEmbedding.norm (mixedEmbedding K (u : K)) ≠ 0 := by
  rw [norm_unit]
  exact one_ne_zero

lemma measurePreserving_unit_smul (u : (𝓞 K)ˣ) :
    MeasurePreserving (fun x : V => u • x) volume volume := by
  refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
  have := map_mulL_volume (norm_mixedEmbedding_unit_ne_zero u)
  rw [norm_unit, inv_one, ENNReal.ofReal_one, one_smul] at this
  exact this

lemma measurableEmbedding_unit_smul (u : (𝓞 K)ˣ) :
    MeasurableEmbedding (fun x : V => u • x) :=
  (mulHomeomorph (norm_mixedEmbedding_unit_ne_zero u)).measurableEmbedding

instance : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)

instance : Countable (𝓞 K)ˣ := by
  have : Countable (𝓞 K) := Subtype.countable
  exact Function.Injective.countable Units.val_injective

lemma setOf_unit_smul_mem_eq {x : V} {u₀ : (𝓞 K)ˣ} (h₀ : u₀ • x ∈ fundamentalCone K) :
    {u : (𝓞 K)ˣ | u • x ∈ fundamentalCone K} =
      (fun ζ => ζ * u₀) '' (Units.torsion K : Set (𝓞 K)ˣ) := by
  ext u
  simp only [mem_ofPred_eq, mem_image, SetLike.mem_coe]
  have hu : u • x = (u * u₀⁻¹) • (u₀ • x) := by
    rw [smul_smul, inv_mul_cancel_right]
  rw [hu, fundamentalCone.unit_smul_mem_iff_mem_torsion h₀]
  refine ⟨fun h => ⟨u * u₀⁻¹, h, inv_mul_cancel_right u u₀⟩, ?_⟩
  rintro ⟨ζ, hζ, rfl⟩
  rwa [mul_inv_cancel_right]

/-- A point of nonzero norm has exactly `torsionOrder K` unit translates in the fundamental
cone. -/
theorem tsum_indicator_unit_smul {x : V} (hx : mixedEmbedding.norm x ≠ 0) :
    ∑' u : (𝓞 K)ˣ, (fundamentalCone K).indicator (1 : V → ℝ≥0∞) (u • x) =
      Units.torsionOrder K := by
  obtain ⟨u₀, h₀⟩ := fundamentalCone.exists_unit_smul_mem hx
  have h1 : (fun u : (𝓞 K)ˣ => (fundamentalCone K).indicator (1 : V → ℝ≥0∞) (u • x)) =
      {u : (𝓞 K)ˣ | u • x ∈ fundamentalCone K}.indicator 1 := by
    ext u
    simp only [Set.indicator_apply, mem_ofPred_eq, Pi.one_apply]
  rw [h1, setOf_unit_smul_mem_eq h₀, ← tsum_subtype]
  simp only [Pi.one_apply, ENNReal.tsum_const, mul_one]
  have e : ENat.card ((fun ζ => ζ * u₀) '' (Units.torsion K : Set (𝓞 K)ˣ)) =
      ENat.card (Units.torsion K : Set (𝓞 K)ˣ) :=
    ENat.card_congr ((Equiv.mulRight u₀).image _).symm
  rw [e, SetLike.coe_sort_coe, ENat.card_eq_coe_natCard]
  simp [Units.torsionOrder]

/-- The real-valued form of `tsum_indicator_unit_smul`. -/
theorem hasSum_indicator_unit_smul {x : V} (hx : mixedEmbedding.norm x ≠ 0) :
    HasSum (fun u : (𝓞 K)ˣ => (fundamentalCone K).indicator (1 : V → ℝ) (u • x))
      (Units.torsionOrder K) := by
  have h := ENNReal.hasSum_toReal (f := fun u : (𝓞 K)ˣ =>
    (fundamentalCone K).indicator (1 : V → ℝ≥0∞) (u • x))
    (by rw [tsum_indicator_unit_smul hx]; exact ENNReal.natCast_ne_top _)
  have hf : ∀ u : (𝓞 K)ˣ, (fundamentalCone K).indicator (1 : V → ℝ≥0∞) (u • x) ≠ ∞ := by
    intro u
    by_cases hu : u • x ∈ fundamentalCone K
    · rw [indicator_of_mem hu]
      simp
    · rw [indicator_of_notMem hu]
      simp
  rw [← ENNReal.tsum_toReal_eq hf, tsum_indicator_unit_smul hx, ENNReal.toReal_natCast] at h
  convert h using 2 with u
  by_cases hu : u • x ∈ fundamentalCone K
  · rw [indicator_of_mem hu, indicator_of_mem hu]
    simp
  · rw [indicator_of_notMem hu, indicator_of_notMem hu]
    simp

lemma tsum_indicator_inv_smul {x : V} (hx : mixedEmbedding.norm x ≠ 0) :
    ∑' u : (𝓞 K)ˣ, (fundamentalCone K).indicator (1 : V → ℝ≥0∞) (u⁻¹ • x) =
      Units.torsionOrder K :=
  ((Equiv.inv (𝓞 K)ˣ).tsum_eq
    (fun u : (𝓞 K)ˣ => (fundamentalCone K).indicator (1 : V → ℝ≥0∞) (u • x))).trans
    (tsum_indicator_unit_smul hx)

lemma hasSum_indicator_inv_smul {x : V} (hx : mixedEmbedding.norm x ≠ 0) :
    HasSum (fun u : (𝓞 K)ˣ => (fundamentalCone K).indicator (1 : V → ℝ) (u⁻¹ • x))
      (Units.torsionOrder K) :=
  (Equiv.inv (𝓞 K)ˣ).hasSum_iff.mpr (hasSum_indicator_unit_smul hx)

lemma measurable_indicator_inv_smul {M : Type*} [AddMonoidWithOne M] [MeasurableSpace M]
    (u : (𝓞 K)ˣ) :
    Measurable fun y : V => (fundamentalCone K).indicator (1 : V → M) (u⁻¹ • y) :=
  (measurable_one.indicator (measurableSet_fundamentalCone K)).comp
    (measurePreserving_unit_smul u⁻¹).measurable

/-! ### Unfolding over the units -/

lemma setLIntegral_unit_smul (u : (𝓞 K)ˣ) (Ψ : V → ℝ≥0∞) :
    ∫⁻ x in fundamentalCone K, Ψ (u • x) =
      ∫⁻ y, (fundamentalCone K).indicator 1 (u⁻¹ • y) * Ψ y := by
  rw [← lintegral_indicator (measurableSet_fundamentalCone K),
    ← (measurePreserving_unit_smul u).lintegral_comp_emb (measurableEmbedding_unit_smul u)
      (fun y => (fundamentalCone K).indicator 1 (u⁻¹ • y) * Ψ y)]
  refine lintegral_congr fun x => ?_
  simp only [inv_smul_smul]
  by_cases hx : x ∈ fundamentalCone K <;> simp [hx]

/-- Unfolding over the units, for nonnegative functions: the translates `u • C` of the
fundamental cone cover almost every point of the mixed space exactly `torsionOrder K` times. -/
theorem tsum_setLIntegral_unit_smul {Ψ : V → ℝ≥0∞} (hΨ : AEMeasurable Ψ) :
    ∑' u : (𝓞 K)ˣ, ∫⁻ x in fundamentalCone K, Ψ (u • x) =
      Units.torsionOrder K * ∫⁻ x, Ψ x := by
  simp_rw [setLIntegral_unit_smul]
  rw [← lintegral_tsum (f := fun u y => (fundamentalCone K).indicator 1 (u⁻¹ • y) * Ψ y)
      fun u => (measurable_indicator_inv_smul u).aemeasurable.mul hΨ,
    ← lintegral_const_mul'' _ hΨ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_norm_ne_zero] with y hy
  rw [ENNReal.tsum_mul_right, tsum_indicator_inv_smul hy]

lemma setIntegral_unit_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : (𝓞 K)ˣ) (Ψ : V → E) :
    ∫ x in fundamentalCone K, Ψ (u • x) =
      ∫ y, (fundamentalCone K).indicator (1 : V → ℝ) (u⁻¹ • y) • Ψ y := by
  rw [← integral_indicator (measurableSet_fundamentalCone K),
    ← (measurePreserving_unit_smul u).integral_comp (measurableEmbedding_unit_smul u)
      (fun y => (fundamentalCone K).indicator (1 : V → ℝ) (u⁻¹ • y) • Ψ y)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inv_smul_smul]
  by_cases hx : x ∈ fundamentalCone K <;> simp [hx]

/-- Unfolding over the units: for an integrable function `Ψ` on the mixed space, the integrals
of its unit translates over the fundamental cone sum to `torsionOrder K • ∫ Ψ`. -/
theorem hasSum_setIntegral_unit_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : V → E} (hΨ : Integrable Ψ) :
    HasSum (fun u : (𝓞 K)ˣ => ∫ x in fundamentalCone K, Ψ (u • x))
      ((Units.torsionOrder K : ℝ) • ∫ x, Ψ x) := by
  set G : (𝓞 K)ˣ → V → E := fun u y =>
    (fundamentalCone K).indicator (1 : V → ℝ) (u⁻¹ • y) • Ψ y with hG
  have hGm : ∀ u, AEStronglyMeasurable (G u) volume := fun u =>
    (measurable_indicator_inv_smul u).aestronglyMeasurable.smul hΨ.aestronglyMeasurable
  have hGn : ∀ u y, ‖G u y‖ₑ = (fundamentalCone K).indicator 1 (u⁻¹ • y) * ‖Ψ y‖ₑ := by
    intro u y
    simp only [hG]
    by_cases h : u⁻¹ • y ∈ fundamentalCone K
    · rw [indicator_of_mem h, indicator_of_mem h]
      simp
    · rw [indicator_of_notMem h, indicator_of_notMem h]
      simp
  have hGi : ∀ u, Integrable (G u) := by
    intro u
    refine hΨ.norm.mono' (hGm u) (Eventually.of_forall fun y => ?_)
    simp only [hG]
    by_cases h : u⁻¹ • y ∈ fundamentalCone K
    · rw [indicator_of_mem h]
      simp
    · rw [indicator_of_notMem h]
      simp
  have hsum : Summable fun u => ∫ y, ‖G u y‖ := by
    simp_rw [integral_norm_eq_lintegral_enorm (hGm _)]
    refine ENNReal.summable_toReal ?_
    simp_rw [hGn, ← setLIntegral_unit_smul]
    rw [tsum_setLIntegral_unit_smul hΨ.aestronglyMeasurable.enorm]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hΨ.hasFiniteIntegral.ne
  have h := hasSum_integral_of_summable_integral_norm hGi hsum
  have hlim : ∫ y, ∑' u, G u y = ∫ y, (Units.torsionOrder K : ℝ) • Ψ y := by
    refine integral_congr_ae ?_
    filter_upwards [ae_norm_ne_zero] with y hy
    exact ((hasSum_indicator_inv_smul hy).smul_const (Ψ y)).tsum_eq
  rw [hlim, integral_smul] at h
  convert h using 2 with u
  exact setIntegral_unit_smul u Ψ

/-! ### The fundamental cone as a dyadic cone -/

/-- The fundamental cone of the mixed space with the norm `mixedEmbedding.norm`, as a dyadic
cone in the sense of `DyadicCone`. -/
def fundamentalDyadicCone : DyadicCone V where
  N := mixedEmbedding.norm
  C := fundamentalCone K
  measurable_N := (mixedEmbedding.continuous_norm K).measurable
  measurableSet_C := measurableSet_fundamentalCone K
  pos _ hx := fundamentalCone.norm_pos_of_mem hx
  smul_mem _ hx _ ht := fundamentalCone.smul_mem_of_mem hx ht.ne'
  N_smul x _ t ht := by rw [mixedEmbedding.norm_smul, abs_of_pos ht, mixedEmbedding.finrank]
  rank_pos := by rw [mixedEmbedding.finrank]; exact Module.finrank_pos

@[simp] lemma fundamentalDyadicCone_N : (fundamentalDyadicCone (K := K)).N = mixedEmbedding.norm :=
  rfl

@[simp] lemma fundamentalDyadicCone_C : (fundamentalDyadicCone (K := K)).C = fundamentalCone K :=
  rfl

/-! ### Coordinates on the fundamental cone -/

lemma normAtPlace_le_norm (w : InfinitePlace K) (x : V) : normAtPlace w x ≤ ‖x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w x) (Finset.mem_univ w)

/-- On the fundamental cone, every coordinate `normAtPlace w x` is comparable to
`N(x) ^ (1 / [K : ℚ])`. -/
theorem exists_normAtPlace_bounds : ∃ r R : ℝ, 0 < r ∧ 0 < R ∧ ∀ x ∈ fundamentalCone K,
    ∀ w : InfinitePlace K,
      r * mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹) ≤ normAtPlace w x ∧
        normAtPlace w x ≤ R * mixedEmbedding.norm x ^ ((finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.mp (fundamentalCone.isBounded_normLeOne K)
  set n := finrank ℚ K
  have hn : 0 < n := Module.finrank_pos
  set R := max R₀ 1
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := zero_lt_one.trans_le hR1
  refine ⟨(R ^ n)⁻¹ * R, R, by positivity, hR0, fun x hx w => ?_⟩
  have hN := fundamentalCone.norm_pos_of_mem hx
  set t := mixedEmbedding.norm x ^ ((n : ℝ)⁻¹)
  have ht : 0 < t := Real.rpow_pos_of_pos hN _
  have htn : t ^ n = mixedEmbedding.norm x := by
    rw [← Real.rpow_mul_natCast hN.le, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
      Real.rpow_one]
  set y := t⁻¹ • x
  have hy : y ∈ fundamentalCone K := fundamentalCone.smul_mem_of_mem hx (inv_ne_zero ht.ne')
  have hNy : mixedEmbedding.norm y = 1 := by
    rw [mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr ht), inv_pow, htn,
      inv_mul_cancel₀ hN.ne']
  have hxy : ∀ v, normAtPlace v x = t * normAtPlace v y := by
    intro v
    rw [normAtPlace_smul, abs_of_pos (inv_pos.mpr ht), ← mul_assoc, mul_inv_cancel₀ ht.ne',
      one_mul]
  have hyR : ∀ v, normAtPlace v y ≤ R := fun v =>
    ((normAtPlace_le_norm v y).trans (hR₀ y ⟨hy, hNy.le⟩)).trans (le_max_left _ _)
  rw [hxy w, mul_comm t]
  refine ⟨mul_le_mul_of_nonneg_right ?_ ht.le, mul_le_mul_of_nonneg_right (hyR w) ht.le⟩
  -- lower bound: `1 = N(y) ≤ (a_w / R) ^ (mult w) * R ^ n`
  set b : InfinitePlace K → ℝ := fun v => (normAtPlace v y / R) ^ mult v
  have hb0 : ∀ v, 0 ≤ b v := fun v => pow_nonneg (div_nonneg (normAtPlace_nonneg v y) hR0.le) _
  have hb1 : ∀ v, b v ≤ 1 := fun v =>
    pow_le_one₀ (div_nonneg (normAtPlace_nonneg v y) hR0.le) ((div_le_one hR0).mpr (hyR v))
  have hprod : ∏ v, b v = (R ^ n)⁻¹ := by
    simp only [b, div_pow, Finset.prod_div_distrib, ← mixedEmbedding.norm_apply, hNy,
      Finset.prod_pow_eq_pow_sum, sum_mult_eq, one_div]
    rfl
  have hle : ∏ v, b v ≤ b w := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
    exact mul_le_of_le_one_right (hb0 w)
      (Finset.prod_le_one₀ (fun v _ => hb0 v) (fun v _ => hb1 v))
  have hbw : b w ≤ normAtPlace w y / R :=
    pow_le_of_le_one (div_nonneg (normAtPlace_nonneg w y) hR0.le)
      ((div_le_one hR0).mpr (hyR w)) mult_ne_zero
  rw [hprod] at hle
  have := hle.trans hbw
  rwa [le_div_iff₀ hR0] at this

end Langlands.Global.Hecke

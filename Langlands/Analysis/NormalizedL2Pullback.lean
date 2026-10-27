import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Normalized pullback on actual L² spaces

For a measurable equivalence `e : X ≃ᵐ Y` and an explicitly supplied scalar
pushforward law `μ.map e = c • ν` with `c : ℝ≥0`, composition with `e` defines
a complex-linear map `Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ` multiplying norms by `√c`.
For `c ≠ 0`, multiplying by `(√c)⁻¹` gives an isometry equivalence whose
inverse is the same construction for `e.symm` and `c⁻¹`. Identity and
contravariant composition laws are included. The measure law is a hypothesis;
nothing here derives it.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace Langlands
namespace NormalizedL2Pullback

universe uX uY uZ

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y}

/-- A scalar pushforward law supplies the actual null-class transport. -/
theorem quasiMeasurePreserving (e : X ≃ᵐ Y) (c : ℝ≥0)
    (hmap : μ.map e = c • ν) : Measure.QuasiMeasurePreserving e μ ν :=
  ⟨e.measurable, hmap ▸ Measure.AbsolutelyContinuous.rfl.smul_left c⟩

/-- Pullback belongs to L² by the supplied finite scalar pushforward law. -/
theorem memLp_comp (e : X ≃ᵐ Y) (c : ℝ≥0) (hmap : μ.map e = c • ν)
    (f : Lp ℂ 2 ν) : MemLp (f ∘ e) 2 μ := by
  apply MemLp.comp_of_map _ e.measurable.aemeasurable
  rw [hmap]
  exact (Lp.memLp f).smul_measure ENNReal.coe_ne_top

/-- Unnormalized pullback between the actual almost-everywhere quotients. -/
def pullback (e : X ≃ᵐ Y) (c : ℝ≥0) (hmap : μ.map e = c • ν) :
    Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_comp e c hmap f).toLp (f ∘ e)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_comp e c hmap (f + g)),
      MemLp.coeFn_toLp (memLp_comp e c hmap f),
      MemLp.coeFn_toLp (memLp_comp e c hmap g),
      Lp.coeFn_add ((memLp_comp e c hmap f).toLp (f ∘ e))
        ((memLp_comp e c hmap g).toLp (g ∘ e)),
      (quasiMeasurePreserving e c hmap).ae_eq_comp (Lp.coeFn_add f g)] with x hfg hf hg hs ha
    simp only [Function.comp_apply, Pi.add_apply] at *
    exact hfg.trans (ha.trans (hs.trans (by rw [hf, hg])).symm)
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_comp e c hmap (a • f)),
      MemLp.coeFn_toLp (memLp_comp e c hmap f),
      Lp.coeFn_smul a ((memLp_comp e c hmap f).toLp (f ∘ e)),
      (quasiMeasurePreserving e c hmap).ae_eq_comp (Lp.coeFn_smul a f)] with x haf hf hs ha
    simp only [Function.comp_apply, Pi.smul_apply, RingHom.id_apply] at *
    exact haf.trans (ha.trans (hs.trans (by rw [hf])).symm)

theorem pullback_apply (e : X ≃ᵐ Y) (c : ℝ≥0) (hmap : μ.map e = c • ν)
    (f : Lp ℂ 2 ν) : pullback e c hmap f = (memLp_comp e c hmap f).toLp (f ∘ e) :=
  rfl

theorem coeFn_pullback (e : X ≃ᵐ Y) (c : ℝ≥0) (hmap : μ.map e = c • ν)
    (f : Lp ℂ 2 ν) : pullback e c hmap f =ᵐ[μ] f ∘ e :=
  MemLp.coeFn_toLp (memLp_comp e c hmap f)

theorem norm_pullback (e : X ≃ᵐ Y) (c : ℝ≥0) (hmap : μ.map e = c • ν)
    (f : Lp ℂ 2 ν) : ‖pullback e c hmap f‖ = (NNReal.sqrt c : ℝ) * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_pullback e c hmap f)]
  have hf : AEStronglyMeasurable f (c • ν) :=
    (Lp.aestronglyMeasurable f).smul_measure c
  rw [eLpNorm_comp_measurePreserving hf ⟨e.measurable, hmap⟩,
    eLpNorm_smul_measure_of_ne_top' ENNReal.ofNat_ne_top c f
      (Lp.aestronglyMeasurable f)]
  simp [ENNReal.smul_def, ENNReal.toReal_mul, Lp.norm_def,
    NNReal.sqrt_eq_rpow]

/-- The positive inverse half-density, viewed as a complex scalar. -/
def normalization (c : ℝ≥0) : ℂ := ((NNReal.sqrt c : ℝ) : ℂ)⁻¹

@[simp] theorem normalization_one : normalization 1 = 1 := by
  simp [normalization]

theorem norm_normalization (c : ℝ≥0) :
    ‖normalization c‖ = (NNReal.sqrt c : ℝ)⁻¹ := by
  simp [normalization]

theorem normalization_mul (c d : ℝ≥0) :
    normalization (c * d) = normalization c * normalization d := by
  simp [normalization, NNReal.sqrt_mul, mul_comm]

theorem normalization_inv (c : ℝ≥0) :
    normalization c⁻¹ = (normalization c)⁻¹ := by
  simp [normalization, NNReal.sqrt_inv]

theorem normalization_ne_zero {c : ℝ≥0} (hc : c ≠ 0) :
    normalization c ≠ 0 := by
  simpa [normalization] using hc

/-- Pullback normalized by the explicit pushforward scalar. -/
def normalized (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearMap := normalization c • pullback e c hmap
  norm_map' f := by
    change ‖normalization c • pullback e c hmap f‖ = ‖f‖
    rw [norm_smul, norm_normalization, norm_pullback, ← mul_assoc,
      inv_mul_cancel₀, one_mul]
    exact_mod_cast (NNReal.sqrt_eq_zero.not.mpr hc)

theorem normalized_apply (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 ν) :
    normalized e c hc hmap f = normalization c • pullback e c hmap f := rfl

theorem coeFn_normalized (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 ν) :
    normalized e c hc hmap f =ᵐ[μ] fun x => normalization c • f (e x) := by
  rw [normalized_apply]
  filter_upwards [Lp.coeFn_smul (normalization c) (pullback e c hmap f),
    coeFn_pullback e c hmap f] with x hs hf
  simpa only [Pi.smul_apply, Function.comp_apply, hf] using hs

/-- The inverse measurable equivalence has the reciprocal pushforward scalar. -/
theorem map_symm (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) : ν.map e.symm = c⁻¹ • μ := by
  have h := e.map_symm_map (μ := μ)
  rw [hmap, Measure.map_smul c e.symm.measurable.aemeasurable] at h
  calc
    ν.map e.symm = c⁻¹ • (c • ν.map e.symm) := by simp [smul_smul, hc]
    _ = c⁻¹ • μ := by rw [h]

/-- The identity measurable equivalence satisfies the law with scalar `1`. -/
theorem map_refl : μ.map (MeasurableEquiv.refl X) = (1 : ℝ≥0) • μ := by
  change μ.map id = (1 : ℝ≥0) • μ
  simp

/-- The scalar laws multiply under composition of measurable equivalences. -/
theorem map_trans (e : X ≃ᵐ Y) (d : Y ≃ᵐ Z) (c b : ℝ≥0)
    {η : Measure Z} (he : μ.map e = c • ν) (hd : ν.map d = b • η) :
    μ.map (e.trans d) = (c * b) • η := by
  change μ.map (d ∘ e) = _
  rw [← Measure.map_map d.measurable e.measurable, he,
    Measure.map_smul c d.measurable.aemeasurable, hd, smul_smul]

@[simp] theorem normalized_refl (f : Lp ℂ 2 μ) :
    normalized (MeasurableEquiv.refl X) 1 one_ne_zero map_refl f = f := by
  apply Lp.ext
  simpa using coeFn_normalized (MeasurableEquiv.refl X) 1 one_ne_zero
    (μ := μ) (ν := μ) map_refl f

/-- Forward pullback reverses the order of composition. -/
theorem normalized_comp (e : X ≃ᵐ Y) (d : Y ≃ᵐ Z) (c b : ℝ≥0)
    (hc : c ≠ 0) (hb : b ≠ 0) {η : Measure Z}
    (he : μ.map e = c • ν) (hd : ν.map d = b • η) (f : Lp ℂ 2 η) :
    normalized e c hc he (normalized d b hb hd f) =
      normalized (e.trans d) (c * b) (mul_ne_zero hc hb)
        (map_trans e d c b he hd) f := by
  apply Lp.ext
  filter_upwards [coeFn_normalized e c hc he (normalized d b hb hd f),
    (quasiMeasurePreserving e c he).ae_eq_comp (coeFn_normalized d b hb hd f),
    coeFn_normalized (e.trans d) (c * b) (mul_ne_zero hc hb)
      (map_trans e d c b he hd) f] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, h₃, smul_smul, normalization_mul]
  rfl

theorem normalized_symm_apply (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 ν) :
    normalized e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap)
      (normalized e c hc hmap f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_normalized e.symm c⁻¹ (inv_ne_zero hc)
      (map_symm e c hc hmap) (normalized e c hc hmap f),
    (quasiMeasurePreserving e.symm c⁻¹ (map_symm e c hc hmap)).ae_eq_comp
      (coeFn_normalized e c hc hmap f)] with y h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, smul_smul, normalization_inv,
    inv_mul_cancel₀ (normalization_ne_zero hc), one_smul, e.apply_symm_apply]

theorem normalized_apply_symm (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 μ) :
    normalized e c hc hmap
      (normalized e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap) f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_normalized e c hc hmap
      (normalized e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap) f),
    (quasiMeasurePreserving e c hmap).ae_eq_comp
      (coeFn_normalized e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap) f)]
    with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, smul_smul, normalization_inv,
    mul_inv_cancel₀ (normalization_ne_zero hc), one_smul, e.symm_apply_apply]

/-- The normalized operator is an actual complex-linear isometry equivalence. -/
def isometryEquiv (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearEquiv :=
    { (normalized e c hc hmap).toLinearMap with
      invFun := normalized e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap)
      left_inv := normalized_symm_apply e c hc hmap
      right_inv := normalized_apply_symm e c hc hmap }
  norm_map' := (normalized e c hc hmap).norm_map

@[simp] theorem isometryEquiv_apply (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 ν) :
    isometryEquiv e c hc hmap f = normalized e c hc hmap f := rfl

@[simp] theorem isometryEquiv_symm_apply (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 μ) :
    (isometryEquiv e c hc hmap).symm f =
      normalized e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap) f := rfl

theorem coeFn_isometryEquiv (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 ν) :
    isometryEquiv e c hc hmap f =ᵐ[μ] fun x => normalization c • f (e x) :=
  coeFn_normalized e c hc hmap f

theorem coeFn_isometryEquiv_symm (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 μ) :
    (isometryEquiv e c hc hmap).symm f =ᵐ[ν]
      fun y => normalization c⁻¹ • f (e.symm y) :=
  coeFn_normalized e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap) f

@[simp] theorem isometryEquiv_refl :
    isometryEquiv (MeasurableEquiv.refl X) 1 one_ne_zero map_refl =
        LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ) := by
  apply LinearIsometryEquiv.ext
  intro f
  exact normalized_refl f

theorem isometryEquiv_symm (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) :
    (isometryEquiv e c hc hmap).symm =
      isometryEquiv e.symm c⁻¹ (inv_ne_zero hc) (map_symm e c hc hmap) := by
  apply LinearIsometryEquiv.ext
  intro f
  rfl

theorem isometryEquiv_trans (e : X ≃ᵐ Y) (d : Y ≃ᵐ Z) (c b : ℝ≥0)
    (hc : c ≠ 0) (hb : b ≠ 0) {η : Measure Z}
    (he : μ.map e = c • ν) (hd : ν.map d = b • η) :
    (isometryEquiv d b hb hd).trans (isometryEquiv e c hc he) =
      isometryEquiv (e.trans d) (c * b) (mul_ne_zero hc hb)
        (map_trans e d c b he hd) := by
  apply LinearIsometryEquiv.ext
  intro f
  exact normalized_comp e d c b hc hb he hd f

end NormalizedL2Pullback
end Langlands

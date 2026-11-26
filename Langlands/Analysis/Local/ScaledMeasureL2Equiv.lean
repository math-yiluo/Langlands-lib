import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! # Changing variables in `L²` for measures proportional under pushforward -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal

namespace Langlands.MeasureTransport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {mX : Measure X} {mY : Measure Y} {c : ℝ≥0∞}
  (e : X ≃ᵐ Y) (h : Measure.map e mX = c • mY)

include h

/-- A nonzero measure rescaling preserves the almost-everywhere filter under the equivalence. -/
theorem ae_pullback_iff (hc : c ≠ 0) {p : Y → Prop} :
    (∀ᵐ x ∂mX, p (e x)) ↔ ∀ᵐ y ∂mY, p y := by
  change (∀ᶠ y in Filter.map e (ae mX), p y) ↔ ∀ᶠ y in ae mY, p y
  rw [e.map_ae, h, ae_ennreal_smul_measure_eq hc]

private theorem map_symm (hc : c ≠ 0) (hct : c ≠ ∞) :
    Measure.map e.symm mY = c⁻¹ • mX := by
  have hs : c • Measure.map e.symm mY = mX := by
    rw [← Measure.map_smul _ e.symm.measurable.aemeasurable, ← h, e.map_symm_map]
  rw [← hs, smul_smul, ENNReal.inv_mul_cancel hc hct, one_smul]

private theorem memLp_pullback (hct : c ≠ ∞) (f : Lp ℂ 2 mY) :
    MemLp (f ∘ e) 2 mX :=
  ((Lp.memLp f).smul_measure hct).comp_measurePreserving ⟨e.measurable, h⟩

private def pullback (hct : c ≠ ∞) (f : Lp ℂ 2 mY) : Lp ℂ 2 mX :=
  (memLp_pullback e h hct f).toLp (f ∘ e)

private theorem coeFn_pullback (hct : c ≠ ∞) (f : Lp ℂ 2 mY) :
    pullback e h hct f =ᵐ[mX] f ∘ e :=
  MemLp.coeFn_toLp (memLp_pullback e h hct f)

private def pullbackLinear (hc : c ≠ 0) (hct : c ≠ ∞) : Lp ℂ 2 mY →ₗ[ℂ] Lp ℂ 2 mX where
  toFun := pullback e h hct
  map_add' f g := by
    apply Lp.ext
    filter_upwards [coeFn_pullback e h hct (f + g), coeFn_pullback e h hct f,
      coeFn_pullback e h hct g, Lp.coeFn_add (pullback e h hct f) (pullback e h hct g),
      (ae_pullback_iff e h hc).mpr (Lp.coeFn_add f g)] with x hsum hf hg hsum' hfg
    simp only [Function.comp_apply, Pi.add_apply] at *
    rw [hsum, hsum', hf, hg, hfg]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [coeFn_pullback e h hct (z • f), coeFn_pullback e h hct f,
      Lp.coeFn_smul z (pullback e h hct f),
      (ae_pullback_iff e h hc).mpr (Lp.coeFn_smul z f)] with x hzf hf hzf' hsmul
    simp only [Function.comp_apply, Pi.smul_apply, RingHom.id_apply] at *
    rw [hzf, hzf', hf, hsmul]

private theorem pullback_symm_pullback (hc : c ≠ 0) (hct : c ≠ ∞) (f : Lp ℂ 2 mY) :
    pullback e.symm (map_symm e h hc hct) (ENNReal.inv_ne_top.mpr hc)
        (pullback e h hct f) = f := by
  apply Lp.ext
  filter_upwards [coeFn_pullback e.symm (map_symm e h hc hct) (ENNReal.inv_ne_top.mpr hc)
    (pullback e h hct f), (ae_pullback_iff e.symm (map_symm e h hc hct)
      (ENNReal.inv_ne_zero.mpr hct)).mpr (coeFn_pullback e h hct f)] with y hleft hright
  exact hleft.trans (hright.trans (congrArg f (e.apply_symm_apply y)))

private def pullbackEquiv (hc : c ≠ 0) (hct : c ≠ ∞) : Lp ℂ 2 mY ≃ₗ[ℂ] Lp ℂ 2 mX where
  __ := pullbackLinear e h hc hct
  invFun := pullback e.symm (map_symm e h hc hct) (ENNReal.inv_ne_top.mpr hc)
  left_inv := pullback_symm_pullback e h hc hct
  right_inv f := pullback_symm_pullback e.symm (map_symm e h hc hct)
    (ENNReal.inv_ne_zero.mpr hct) (ENNReal.inv_ne_top.mpr hc) f

private theorem norm_pullback (hct : c ≠ ∞) (f : Lp ℂ 2 mY) :
    ‖pullback e h hct f‖ = c.toReal ^ (2 : ℝ≥0∞).toReal⁻¹ * ‖f‖ := by
  rw [pullback, Lp.norm_toLp,
    eLpNorm_comp_measurePreserving ((Lp.memLp f).smul_measure hct).aestronglyMeasurable
      (show MeasurePreserving e mX (c • mY) from ⟨e.measurable, h⟩),
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num) c,
    Lp.norm_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    one_div, ENNReal.toReal_inv]

/-- Pullback is a continuous linear equivalence if the pushforward differs by a
positive finite measure factor. It takes each class to the class of its pullback. -/
def l2Equiv (hc : c ≠ 0) (hct : c ≠ ∞) : Lp ℂ 2 mY ≃L[ℂ] Lp ℂ 2 mX :=
  ContinuousLinearEquiv.ofHomothety (pullbackEquiv e h hc hct) _
    (Real.rpow_pos_of_pos (ENNReal.toReal_pos hc hct) _) (norm_pullback e h hct)

theorem coeFn_l2Equiv (hc : c ≠ 0) (hct : c ≠ ∞) (f : Lp ℂ 2 mY) :
    l2Equiv e h hc hct f =ᵐ[mX] f ∘ e :=
  coeFn_pullback e h hct f

theorem coeFn_l2Equiv_symm (hc : c ≠ 0) (hct : c ≠ ∞) (f : Lp ℂ 2 mX) :
    (l2Equiv e h hc hct).symm f =ᵐ[mY] f ∘ e.symm :=
  coeFn_pullback e.symm (map_symm e h hc hct) (ENNReal.inv_ne_top.mpr hc) f

end Langlands.MeasureTransport

import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Group.Units

/-! # Local comparison of additive and multiplicative Haar measure on units -/

noncomputable section
set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

namespace Langlands.Analysis.UnitGroupHaar

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

private def leftDet : Aˣ →* ℝˣ :=
  LinearEquiv.det.comp (Units.mulLeftLinearEquiv ℝ A)

private theorem coe_leftDet (g : Aˣ) :
    (leftDet g : ℝ) = LinearMap.det ((Units.mulLeftLinearEquiv ℝ A g).toLinearMap) :=
  LinearEquiv.coe_det _

private def weightReal (g : Aˣ) : ℝ := |((leftDet g : ℝˣ) : ℝ)⁻¹|

private def weight (g : Aˣ) : ℝ≥0∞ := ENNReal.ofReal (weightReal g)

private theorem weightReal_pos (g : Aˣ) : 0 < weightReal g :=
  abs_pos.mpr (inv_ne_zero (Units.ne_zero (leftDet g)))

private theorem weight_mul (g h : Aˣ) : weight (g * h) = weight g * weight h := by
  unfold weight weightReal
  rw [map_mul, Units.val_mul, mul_inv, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]

omit [NormedAlgebra ℝ A] in
private theorem val_image_mul_preimage (g : Aˣ) (s : Set Aˣ) :
    Units.val '' ((fun h => g * h) ⁻¹' s) =
      (fun x : A => (g : A) * x) ⁻¹' (Units.val '' s) := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨g * h, hh, rfl⟩
  · rintro ⟨h, hh, heq⟩
    refine ⟨g⁻¹ * h, ?_, ?_⟩
    · change g * (g⁻¹ * h) ∈ s
      rw [mul_inv_cancel_left]
      exact hh
    · change (↑g⁻¹ : A) * ↑h = x
      rw [heq, Units.inv_mul_cancel_left]

private theorem continuous_weightReal : Continuous (weightReal : Aˣ → ℝ) := by
  have hdet : Continuous (fun g : Aˣ => (leftDet g : ℝ)) := by
    simp only [coe_leftDet, Units.toLinearMap_mulLeftLinearEquiv]
    exact ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.mul ℝ A).continuous.comp Units.continuous_val)
  exact (hdet.inv₀ fun g => Units.ne_zero (leftDet g)).abs

variable [FiniteDimensional ℝ A] [CompleteSpace A] [MeasurableSpace A] [BorelSpace A]

omit [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] in
/-- The chart measurable space on units is Borel for the units topology. -/
theorem borelSpace_units : BorelSpace Aˣ where
  measurable_eq := by
    change MeasurableSpace.comap (Units.val : Aˣ → A) _ = borel Aˣ
    rw [BorelSpace.measurable_eq (α := A), ← borel_comap]
    exact congrArg (fun t : TopologicalSpace Aˣ => @borel Aˣ t)
      Units.isOpenEmbedding_val.isInducing.eq_induced.symm

attribute [local instance] borelSpace_units

variable (μ : Measure A) [IsAddHaarMeasure μ]

private theorem map_comap_val_mul_left (g : Aˣ) :
    (μ.comap (Units.val : Aˣ → A)).map (fun h => g * h) =
      weight g • μ.comap (Units.val : Aˣ → A) := by
  let e : Aˣ → A := Units.val
  have he : MeasurableEmbedding e := Units.isOpenEmbedding_val.measurableEmbedding
  let L : A →ₗ[ℝ] A := (Units.mulLeftLinearEquiv ℝ A g).toLinearMap
  have hdet : LinearMap.det L ≠ 0 := coe_leftDet g ▸ Units.ne_zero (leftDet g)
  have hscale : μ.map L = weight g • μ := by
    rw [map_linearMap_addHaar_eq_smul_addHaar μ hdet, weight, weightReal, coe_leftDet]
  have hm : Measurable (fun h : Aˣ => g * h) := (continuous_const.mul continuous_id).measurable
  ext s hs
  rw [Measure.map_apply hm hs,
    Measure.comap_apply e he.injective he.measurableSet_image' μ (hm hs)]
  rw [val_image_mul_preimage g s]
  change μ (L ⁻¹' (e '' s)) = _
  rw [← Measure.map_apply L.continuous_of_finiteDimensional.measurable (he.measurableSet_image' hs),
    hscale, Measure.smul_apply, Measure.smul_apply,
    Measure.comap_apply e he.injective he.measurableSet_image' μ hs]

private def weightedMeasure : Measure Aˣ :=
  (μ.comap Units.val).withDensity weight

private theorem weightedMeasure_leftInvariant : IsMulLeftInvariant (weightedMeasure μ) := by
  let ν : Measure Aˣ := μ.comap Units.val
  let η := weightedMeasure μ
  have hw : Measurable (weight : Aˣ → ℝ≥0∞) := continuous_weightReal.measurable.ennreal_ofReal
  constructor
  intro g
  let f : Aˣ → Aˣ := fun h => g * h
  have hf : Measurable f := (continuous_const.mul continuous_id).measurable
  have hg0 : weight g ≠ 0 := (ENNReal.ofReal_pos.mpr (weightReal_pos g)).ne'
  have hgt : weight g ≠ ∞ := ENNReal.ofReal_ne_top
  ext s hs
  apply (ENNReal.mul_right_inj hg0 hgt).mp
  calc
    weight g * η.map f s =
        weight g * ∫⁻ h, (f ⁻¹' s).indicator weight h ∂ν := by
      rw [Measure.map_apply hf hs]
      change _ * ν.withDensity weight (f ⁻¹' s) = _
      rw [withDensity_apply _ (hf hs), lintegral_indicator (hf hs)]
    _ = ∫⁻ h, s.indicator weight (f h) ∂ν := by
      rw [← lintegral_const_mul' _ _ hgt]
      refine lintegral_congr fun h => ?_
      by_cases hh : f h ∈ s
      · rw [indicator_of_mem (show h ∈ f ⁻¹' s from hh), indicator_of_mem hh]
        exact (weight_mul g h).symm
      · rw [indicator_of_notMem (show h ∉ f ⁻¹' s from hh), indicator_of_notMem hh, mul_zero]
    _ = ∫⁻ h, s.indicator weight h ∂ν.map f := (lintegral_map (hw.indicator hs) hf).symm
    _ = weight g * η s := by
      rw [show ν.map f = weight g • ν from map_comap_val_mul_left μ g,
        lintegral_smul_measure, lintegral_indicator hs]
      exact congrArg (weight g * ·) (withDensity_apply weight hs).symm

omit [FiniteDimensional ℝ A] in
private theorem weightedMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (weightedMeasure μ) := by
  constructor
  intro t ht
  let e : Aˣ → A := Units.val
  let ν : Measure Aˣ := μ.comap e
  have he : MeasurableEmbedding e := Units.isOpenEmbedding_val.measurableEmbedding
  have hν : ν t < ∞ := by
    rw [Measure.comap_apply e he.injective he.measurableSet_image' μ ht.measurableSet]
    exact (ht.image Units.continuous_val).measure_lt_top
  obtain ⟨b, hb⟩ := (ht.image continuous_weightReal).bddAbove
  change ν.withDensity weight t < ∞
  rw [withDensity_apply _ ht.measurableSet]
  calc
    _ ≤ ∫⁻ _ in t, ENNReal.ofReal b ∂ν := by
      apply setLIntegral_mono' ht.measurableSet
      intro g hg
      exact ENNReal.ofReal_le_ofReal (hb (mem_image_of_mem _ hg))
    _ < ∞ := by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν

/-- On a compact region of the unit group the ambient additive Haar
measure pulled back through the open chart is dominated by a finite
constant times the specified multiplicative Haar measure. -/
theorem restrict_comap_val_le (η : Measure Aˣ) [IsHaarMeasure η]
    (t : Set Aˣ) (ht : IsCompact t) :
    ∃ c : ℝ≥0, (μ.comap (Units.val : Aˣ → A)).restrict t ≤ c • η.restrict t := by
  let ν : Measure Aˣ := μ.comap Units.val
  let m := weightedMeasure μ
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology Aˣ := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let : IsMulLeftInvariant m := weightedMeasure_leftInvariant μ
  let : IsFiniteMeasureOnCompacts m := weightedMeasure_finiteOnCompacts μ
  let a := haarScalarFactor m η
  have ha : m = a • η := isMulLeftInvariant_eq_smul m η
  obtain ⟨b, hb, hbound⟩ := ht.exists_forall_le' continuous_weightReal.continuousOn
    (a := (0 : ℝ)) (fun g _ => weightReal_pos g)
  let c : ℝ≥0 := ⟨b, hb.le⟩
  have hc0 : c ≠ 0 := fun h => hb.ne' (congrArg NNReal.toReal h)
  have hle : c • ν.restrict t ≤ m.restrict t := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs]
    change (c : ℝ≥0∞) * ν (s ∩ t) ≤ ν.withDensity weight (s ∩ t)
    rw [withDensity_apply _ (hs.inter ht.measurableSet), ← setLIntegral_const]
    apply setLIntegral_mono' (hs.inter ht.measurableSet)
    intro g hg
    rw [ENNReal.coe_nnreal_eq c]
    exact ENNReal.ofReal_le_ofReal (hbound g hg.2)
  refine ⟨c⁻¹ * a, ?_⟩
  rw [ha, Measure.restrict_smul] at hle
  have hscaled : c⁻¹ • (c • ν.restrict t) ≤ c⁻¹ • (a • η.restrict t) := by
    refine Measure.le_iff.mpr fun s hs => ?_
    exact mul_le_mul' le_rfl (Measure.le_iff.mp hle s hs)
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul, smul_smul] at hscaled

section Product

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
  [SecondCountableTopology H]

/-- For a function constant in the second coordinate of a compact product
patch, its additive integral in the first coordinate is bounded by a
finite multiple of its integral against the product group's Haar measure. -/
theorem exists_lintegral_productPatch_le (η : Measure G) [IsHaarMeasure η]
    (e : G ≃ₜ* Aˣ × H) (t : Set A) (ht : IsCompact t)
    (htu : t ⊆ range (Units.val : Aˣ → A))
    (s : Set H) (hso : IsOpen s) (hsc : IsCompact s) (hsn : s.Nonempty) :
    ∃ C : ℝ≥0, ∀ (f : G → ℝ≥0∞) (p : A → ℝ≥0∞), Measurable f →
      (∀ a : Aˣ, (a : A) ∈ t → ∀ b ∈ s, f (e.symm (a, b)) = p a) →
      ∫⁻ x in t, p x ∂μ ≤
        C * ∫⁻ g in e ⁻¹' ((Units.val ⁻¹' t) ×ˢ s), f g ∂η := by
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology Aˣ := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let : SigmaCompactSpace Aˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  let νa : Measure Aˣ := Measure.haar
  let νh : Measure H := Measure.haar
  let ν := νa.prod νh
  let M := η.map e
  let : IsHaarMeasure M := e.isHaarMeasure_map η
  let c := haarScalarFactor M ν
  have hc : M = c • ν := isMulLeftInvariant_eq_smul M ν
  have hc0 : 0 < c := haarScalarFactor_pos_of_isHaarMeasure M ν
  let T : Set Aˣ := Units.val ⁻¹' t
  have hT : IsCompact T := Units.isOpenEmbedding_val.isEmbedding.isCompact_iff.mpr
    (by rwa [image_preimage_eq_of_subset htu])
  let P : Set (Aˣ × H) := T ×ˢ s
  let Q : Set G := e ⁻¹' P
  obtain ⟨d, hd⟩ := restrict_comap_val_le μ νa T hT
  let b : ℝ≥0∞ := (c : ℝ≥0∞) * νh s
  have hb0 : b ≠ 0 := mul_ne_zero (by exact_mod_cast hc0.ne') ((hso.measure_pos νh hsn).ne')
  have hbt : b ≠ ∞ := (ENNReal.mul_lt_top ENNReal.coe_lt_top hsc.measure_lt_top).ne
  let B : ℝ≥0∞ := (d : ℝ≥0∞) * b⁻¹
  have hBt : B ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.mpr hb0)
  refine ⟨B.toNNReal, ?_⟩
  intro f p hf heq
  change (∫⁻ x in t, p x ∂μ) ≤ (B.toNNReal : ℝ≥0∞) * ∫⁻ g in Q, f g ∂η
  let v : Aˣ → A := Units.val
  have hv : MeasurableEmbedding v := Units.isOpenEmbedding_val.measurableEmbedding
  let p' : Aˣ → ℝ≥0∞ := p ∘ v
  have hmap : ((μ.comap v).restrict T).map v = μ.restrict t := by
    rw [← hv.restrict_map, hv.map_comap, Measure.restrict_restrict_of_subset htu]
  have hη :
      ∫⁻ g in Q, f g ∂η = b * ∫⁻ a in T, p' a ∂νa := by
    let f' : Aˣ × H → ℝ≥0∞ := f ∘ e.symm
    have hf' : Measurable f' := hf.comp e.symm.continuous.measurable
    have hm : MeasurePreserving (fun g => e g) η M :=
      ⟨e.continuous.measurable, rfl⟩
    have he : MeasurableEmbedding (fun g => e g) :=
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    calc
      _ = ∫⁻ z in P, f' z ∂M := by
        simpa only [f', Function.comp_apply, e.symm_apply_apply] using
          hm.setLIntegral_comp_preimage_emb he f' P
      _ = (c : ℝ≥0∞) * (∫⁻ z in P, f' z ∂ν) := by
        rw [hc, Measure.restrict_smul, lintegral_smul_measure]
        rfl
      _ = (c : ℝ≥0∞) * (∫⁻ a in T, ∫⁻ y in s, f' (a, y) ∂νh ∂νa) := by
        rw [setLIntegral_prod f' hf'.aemeasurable]
      _ = (c : ℝ≥0∞) * (∫⁻ a in T, νh s * p' a ∂νa) := by
        congr 1
        apply setLIntegral_congr_fun hT.measurableSet
        intro a ha
        change (∫⁻ y in s, f (e.symm (a, y)) ∂νh) = νh s * p' a
        rw [setLIntegral_congr_fun hso.measurableSet (g := fun _ => p' a)
          (fun y hy => heq a ha y hy), setLIntegral_const, mul_comm]
      _ = b * ∫⁻ a in T, p' a ∂νa := by
        rw [lintegral_const_mul' _ _ hsc.measure_lt_top.ne, ← mul_assoc]
  rw [ENNReal.coe_toNNReal hBt, hη]
  calc
    ∫⁻ x in t, p x ∂μ = ∫⁻ a in T, p' a ∂μ.comap v := by
      rw [← hmap, hv.lintegral_map]
      rfl
    _ ≤ (d : ℝ≥0∞) * ∫⁻ a in T, p' a ∂νa := by
      rw [← smul_eq_mul, ← lintegral_smul_measure, Measure.coe_nnreal_smul]
      exact lintegral_mono' hd (le_refl p')
    _ = B * (b * ∫⁻ a in T, p' a ∂νa) := by
      rw [← mul_assoc, show B * b = (d : ℝ≥0∞) by
        rw [show B = (d : ℝ≥0∞) * b⁻¹ from rfl, mul_assoc,
          ENNReal.inv_mul_cancel hb0 hbt, mul_one]]

end Product

end Langlands.Analysis.UnitGroupHaar

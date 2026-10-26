import Langlands.Analysis.Local.QuotientCompactOpenOrbitStatement
import Langlands.Analysis.Local.QuotientFunctional
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported

universe uG

variable {G : Type uG} [Group G]

@[simp] theorem leftQuotientMap_subgroup_mul (H : Subgroup G) (h : H) (x : G) :
    leftQuotientMap H ((h : G) * x) = leftQuotientMap H x := by
  apply Quotient.sound
  change QuotientGroup.rightRel H ((h : G) * x) x
  rw [QuotientGroup.rightRel_apply]
  simp [mul_inv_rev, mul_assoc]

/-- Pulling a quotient function back before averaging factors it out of the
actual subgroup integral. No integrability premise is needed for this identity. -/
theorem quotientAverage_pullback_mul (H : Subgroup G)
    [MeasurableSpace H] [MeasurableMul H]
    (μH : Measure H) [IsMulRightInvariant μH]
    (φ : LeftQuotient H → ℂ) (f : G → ℂ) (z : LeftQuotient H) :
    quotientAverage H μH (fun x => φ (leftQuotientMap H x) * f x) z =
      φ z * quotientAverage H μH f z := by
  induction z using Quotient.inductionOn with
  | h x =>
    simp only [quotientAverage_mk, leftQuotientMap_subgroup_mul]
    exact integral_const_mul _ _

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The compact-open subgroup in H cut out by conjugating into K is open. -/
theorem isOpen_compactOpenOrbitStabilizer (H : Subgroup G)
    (K : OpenSubgroup G) (g : G) :
    IsOpen {h : H | g⁻¹ * (h : G) * g ∈ K} :=
  K.isOpen.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- Closedness of H makes the same subgroup compact when K is compact. -/
theorem isCompact_compactOpenOrbitStabilizer (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) :
    IsCompact {h : H | g⁻¹ * (h : G) * g ∈ K} := by
  let e : G ≃ₜ G := (Homeomorph.mulLeft g⁻¹).trans (Homeomorph.mulRight g)
  exact (e.isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal).isCompact_preimage hK

end Topology

section Indicator

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) [MeasurableSpace H] [BorelSpace H]
variable (μH : Measure H) [IsMulRightInvariant μH]

/-- Averaging the indicator of gK on its actual quotient gives the stabilizer
mass on the image orbit and zero outside it. -/
theorem quotientAverage_compactOpen_leftCoset_indicator
    (K : OpenSubgroup G) (g : G) (z : LeftQuotient H) :
    quotientAverage H μH
      ({x : G | g⁻¹ * x ∈ K}.indicator (fun _ => (1 : ℂ))) z =
      ((fun k : G => leftQuotientMap H (g * k)) '' (K : Set G)).indicator
        (fun _ => ((μH {h : H | g⁻¹ * (h : G) * g ∈ K}).toReal : ℂ)) z := by
  classical
  let C := (fun k : G => leftQuotientMap H (g * k)) '' (K : Set G)
  let S := {h : H | g⁻¹ * (h : G) * g ∈ K}
  change _ = C.indicator (fun _ => ((μH S).toReal : ℂ)) z
  by_cases hz : z ∈ C
  · obtain ⟨k, hk, rfl⟩ := hz
    rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hk)]
    change quotientAverage H μH _ (leftQuotientMap H (g * k)) = _
    rw [leftQuotientMap_apply, quotientAverage_mk]
    have heq : (fun h : H =>
        {x : G | g⁻¹ * x ∈ K}.indicator (fun _ => (1 : ℂ)) ((h : G) * (g * k))) =
        S.indicator (fun _ => (1 : ℂ)) := by
      funext h
      have hmem : g⁻¹ * ((h : G) * (g * k)) ∈ K ↔ g⁻¹ * (h : G) * g ∈ K := by
        rw [← mul_assoc, ← mul_assoc]
        exact K.toSubgroup.mul_mem_cancel_right hk
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, S, hmem]
    rw [heq, integral_indicator_const _
      (isOpen_compactOpenOrbitStabilizer H K g).measurableSet]
    simp [S, measureReal_def, Complex.real_smul]
  · rw [Set.indicator_of_notMem hz]
    induction z using Quotient.inductionOn with
    | h x =>
      rw [quotientAverage_mk]
      have heq : (fun h : H =>
          {y : G | g⁻¹ * y ∈ K}.indicator (fun _ => (1 : ℂ)) ((h : G) * x)) = 0 := by
        funext h
        apply Set.indicator_of_notMem
        intro hh
        apply hz
        refine ⟨g⁻¹ * ((h : G) * x), hh, ?_⟩
        simp only [mul_inv_cancel_left, leftQuotientMap_subgroup_mul]
        rfl
      rw [heq]
      simp

/-- The shared cutoff-test formula uses the actual quotientAverage and retains
the unnormalized Haar mass of the conjugate intersection. -/
theorem quotientAverage_compactOpen_leftCoset_pullback
    (K : OpenSubgroup G) (g : G) (φ : LeftQuotient H → ℂ) (z : LeftQuotient H) :
    quotientAverage H μH
      ({x : G | g⁻¹ * x ∈ K}.indicator (fun x => φ (leftQuotientMap H x))) z =
      ((fun k : G => leftQuotientMap H (g * k)) '' (K : Set G)).indicator
        (fun y => ((μH {h : H | g⁻¹ * (h : G) * g ∈ K}).toReal : ℂ) * φ y) z := by
  classical
  have heq : {x : G | g⁻¹ * x ∈ K}.indicator (fun x => φ (leftQuotientMap H x)) =
      fun x => φ (leftQuotientMap H x) *
        {x : G | g⁻¹ * x ∈ K}.indicator (fun _ => (1 : ℂ)) x := by
    funext x
    by_cases hx : g⁻¹ * x ∈ K <;> simp [hx]
  rw [heq, quotientAverage_pullback_mul,
    quotientAverage_compactOpen_leftCoset_indicator]
  by_cases hz : z ∈ (fun k : G => leftQuotientMap H (g * k)) '' (K : Set G) <;>
    simp [Set.indicator_apply, mul_comm]

end Indicator

section Restriction

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
variable (μG : Measure G) (μH : Measure H)
variable [IsHaarMeasure μG] [μG.Regular]
variable [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]

include hH in
/-- Compatibility tested against a quotient pullback cut off on gK. -/
theorem IsCompatible.integral_compactOpenOrbit
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (μ : Measure (LeftQuotient H)) (hμ : IsCompatible H μG μH μ)
    (g : G) (φ : LeftQuotient H → ℝ) (hφ : Continuous φ) :
    (μH {h : H | g⁻¹ * (h : G) * g ∈ K}).toReal *
        (∫ z in (fun k : G => leftQuotientMap H (g * k)) '' (K : Set G), φ z ∂μ) =
      ∫ k in (K : Set G), φ (leftQuotientMap H (g * k)) ∂μG := by
  classical
  let := leftQuotient_t2Space H hH
  let q := leftQuotientMap H
  let A := {x : G | g⁻¹ * x ∈ K}
  let C := (fun k : G => q (g * k)) '' (K : Set G)
  let c := μH {h : H | g⁻¹ * (h : G) * g ∈ K}
  let f : G → ℝ := A.indicator (fun x => φ (q x))
  have hq : Continuous q := (leftQuotient_isOpenQuotientMap H).continuous
  have hAc : IsCompact A := (Homeomorph.mulLeft g⁻¹).isClosedEmbedding.isCompact_preimage hK
  have hAcl : IsClopen A :=
    ⟨K.isClosed.preimage (continuous_const.mul continuous_id),
      K.isOpen.preimage (continuous_const.mul continuous_id)⟩
  have hfc : Continuous f := hAcl.continuous_indicator (hφ.comp hq)
  have hfs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact hAc Set.support_indicator_subset
  have hCc : IsCompact C := hK.image (hq.comp (continuous_const.mul continuous_id))
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hav : quotientAverage H μH (fun x => (f x : ℂ)) =
      fun z => ((c.toReal * C.indicator φ z : ℝ) : ℂ) := by
    have hf : (fun x => (f x : ℂ)) =
        A.indicator (fun x => (φ (q x) : ℂ)) := by
      funext x
      by_cases hx : x ∈ A <;> simp [f, hx]
    rw [hf]
    funext z
    change quotientAverage H μH
      ({x : G | g⁻¹ * x ∈ K}.indicator (fun x => (φ (leftQuotientMap H x) : ℂ))) z = _
    rw [quotientAverage_compactOpen_leftCoset_pullback H μH K g (fun z => (φ z : ℂ)) z]
    change C.indicator (fun z => (c.toReal : ℂ) * (φ z : ℂ)) z = _
    by_cases hz : z ∈ C <;> simp [hz]
  have htest := hμ.integral_formula (fun x => (f x : ℂ))
    (Complex.continuous_ofReal.comp hfc) (hfs.comp_left (g := Complex.ofReal) rfl)
  rw [hav, integral_complex_ofReal, integral_complex_ofReal] at htest
  have hreal := Complex.ofReal_injective htest
  rw [integral_const_mul, integral_indicator hCm] at hreal
  change c.toReal * (∫ z in C, φ z ∂μ) = _
  rw [hreal, ← integral_mul_left_eq_self f g]
  have heq : (fun k => f (g * k)) =
      (K : Set G).indicator (fun k => φ (q (g * k))) := by
    funext k
    by_cases hk : k ∈ K <;> simp [f, A, Set.indicator_apply, hk]
  rw [heq, integral_indicator K.isOpen.measurableSet]

/-- Exact published compact-open orbit restriction formula. -/
theorem compactOpenOrbitMeasure : CompactOpenOrbitMeasureStatement := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ _ _ μG μH _ _ _ _ _ K hK μ hμ g
  let := leftQuotient_t2Space H hH
  let := leftQuotient_locallyCompactSpace H
  let : μ.Regular := hμ.regular
  let q := leftQuotientMap H
  let C := (fun k : G => q (g * k)) '' (K : Set G)
  let S := {h : H | g⁻¹ * (h : G) * g ∈ K}
  let c := μH S
  let κ := μG.restrict (K : Set G)
  have hSo : IsOpen S := isOpen_compactOpenOrbitStabilizer H K g
  have hSc : IsCompact S := isCompact_compactOpenOrbitStabilizer H hH K hK g
  have hcpos : 0 < c := hSo.measure_pos μH ⟨1, by simp [S]⟩
  have hcfin : c < ⊤ := hSc.measure_lt_top
  refine ⟨hcpos, hcfin, ?_⟩
  change μ.restrict C = c⁻¹ • Measure.map (fun k : G => q (g * k)) κ
  have hq : Continuous q := (leftQuotient_isOpenQuotientMap H).continuous
  have hp : Continuous (fun k : G => q (g * k)) :=
    hq.comp (continuous_const.mul continuous_id)
  have hCc : IsCompact C := hK.image hp
  let : IsFiniteMeasure κ := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  let : κ.Regular := Measure.Regular.restrict_of_measure_ne_top hK.measure_lt_top.ne
  let : (μ.restrict C).Regular :=
    Measure.Regular.restrict_of_measure_ne_top hCc.measure_lt_top.ne
  let : (Measure.map (fun k : G => q (g * k)) κ).InnerRegular :=
    Measure.InnerRegular.map_of_continuous hp
  let : (c • μ.restrict C).Regular := Measure.Regular.smul hcfin.ne
  have hscaled : c • μ.restrict C = Measure.map (fun k : G => q (g * k)) κ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro φ
    rw [integral_smul_measure,
      integral_map (f := fun z => φ z) hp.measurable.aemeasurable
        (show AEStronglyMeasurable (fun z => φ z) _ from φ.continuous.aestronglyMeasurable)]
    exact IsCompatible.integral_compactOpenOrbit H hH μG μH K hK μ hμ g φ φ.continuous
  rw [← hscaled, smul_smul, ENNReal.inv_mul_cancel hcpos.ne' hcfin.ne, one_smul]

end Restriction

end Langlands.QuotientIntegration

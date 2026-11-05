import Langlands.Analysis.Local.NormalSubgroupHaarModulus
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Modular characters on closed normal subgroups -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure CompactlySupportedContinuousMap
open scoped CompactlySupported NNReal

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (η : Measure H) [IsFiniteMeasureOnCompacts η] [IsMulRightInvariant η]

/-- The Riesz lift of a quotient measure using a right-invariant fiber measure.
Left invariance of the fiber measure is not required. -/
def rightQuotientLift (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν] :
    Measure G :=
  RealRMK.rieszMeasure
    ((integralPositiveLinearMap ν).comp (quotientAverageRealPositive H hH η))

instance rightQuotientLift_regular (ν : Measure (LeftQuotient H))
    [IsFiniteMeasureOnCompacts ν] : (rightQuotientLift H hH η ν).Regular := by
  unfold rightQuotientLift
  infer_instance

theorem integral_rightQuotientLift (ν : Measure (LeftQuotient H))
    [IsFiniteMeasureOnCompacts ν] (f : C_c(G, ℝ)) :
    (∫ g, f g ∂rightQuotientLift H hH η ν) =
      ∫ q, quotientAverageRealPositive H hH η f q ∂ν := by
  rw [rightQuotientLift, RealRMK.integral_rieszMeasure]
  rfl

theorem rightQuotientLift_rightInvariant (ν : Measure (LeftQuotient H))
    [IsFiniteMeasureOnCompacts ν]
    (hν : ∀ g : G, MeasurePreserving (rightTranslate H g) ν ν) :
    (rightQuotientLift H hH η ν).IsMulRightInvariant := by
  let := leftQuotient_t2Space H hH
  constructor
  intro g
  have : (Measure.map (fun x => x * g) (rightQuotientLift H hH η ν)).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f x ∂Measure.map (Homeomorph.mulRight g).toMeasurableEquiv
    (rightQuotientLift H hH η ν)) = _
  rw [integral_map_equiv (Homeomorph.mulRight g).toMeasurableEquiv (fun x => f x)]
  change (∫ x, compactRightTranslate g f x ∂rightQuotientLift H hH η ν) = _
  rw [integral_rightQuotientLift, integral_rightQuotientLift]
  simp_rw [compactAveraging_rightTranslate H η (quotientAverageRealPositive H hH η)
    (fun f x => rfl) g f]
  exact (hν g).integral_comp (rightTranslate H g).toMeasurableEquiv.measurableEmbedding _

theorem rightQuotientLift_ne_zero [IsOpenPosMeasure η]
    (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν] [IsOpenPosMeasure ν] :
    rightQuotientLift H hH η ν ≠ 0 := by
  let := leftQuotient_t2Space H hH
  obtain ⟨f, hfc, hf0, hf1⟩ :
      ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 :=
    exists_continuous_nonneg_pos 1
  let f₀ : C_c(G, ℝ) := ⟨f, hfc⟩
  let A := quotientAverageRealPositive H hH η f₀
  have hA0 : 0 ≤ A := (quotientAverageRealPositive H hH η).map_nonneg hf0
  have hA1 : A (Quotient.mk _ (1 : G)) ≠ 0 := by
    apply ne_of_gt
    change 0 < ∫ h : H, f₀ (h.val * 1) ∂η
    apply integral_pos_of_integrable_nonneg_nonzero
      (f₀.continuous.comp (continuous_subtype_val.mul_const 1))
      (integrable_subgroup_mul H hH η f₀ 1) (fun h => hf0 _)
      (x := (1 : H))
    change f ((1 : H).val * 1) ≠ 0
    simpa only [OneMemClass.coe_one, one_mul] using hf1
  have hpos : 0 < ∫ q, A q ∂ν :=
    A.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      A.hasCompactSupport hA0 hA1
  intro hz
  have hi := integral_rightQuotientLift H hH η ν f₀
  rw [hz, integral_zero_measure] at hi
  exact (ne_of_gt hpos) hi.symm

section Normal

variable [H.Normal]
  [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

/-- Right Haar measure of the quotient group, on the actual left-coset space. -/
def normalQuotientRightHaar : Measure (LeftQuotient H) :=
  Measure.map (normalLeftQuotientHomeomorph H).symm (haar : Measure (G ⧸ H)).inv

instance normalQuotientRightHaar_regular : (normalQuotientRightHaar H).Regular :=
  Measure.Regular.map (normalLeftQuotientHomeomorph H).symm

instance normalQuotientRightHaar_openPos : IsOpenPosMeasure (normalQuotientRightHaar H) := by
  unfold normalQuotientRightHaar
  exact (normalLeftQuotientHomeomorph H).symm.continuous.isOpenPosMeasure_map
    (normalLeftQuotientHomeomorph H).symm.surjective

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] in
theorem normalQuotientRightHaar_invariant (g : G) :
    MeasurePreserving (rightTranslate H g) (normalQuotientRightHaar H)
      (normalQuotientRightHaar H) := by
  let e := (normalLeftQuotientHomeomorph H).symm
  refine ⟨(rightTranslate H g).continuous.measurable, ?_⟩
  change Measure.map (rightTranslate H g) (Measure.map e (haar : Measure (G ⧸ H)).inv) =
    Measure.map e (haar : Measure (G ⧸ H)).inv
  have hc : (rightTranslate H g) ∘ e =
      e ∘ (fun x : G ⧸ H => x * (g : G ⧸ H)) := by
    funext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  rw [Measure.map_map (rightTranslate H g).continuous.measurable e.continuous.measurable,
    hc, ← Measure.map_map e.continuous.measurable (measurable_mul_const _),
    map_mul_right_eq_self]

end Normal

omit H hH η [T2Space G] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  [IsFiniteMeasureOnCompacts η] [IsMulRightInvariant η] in
/-- Left translation of inverse Haar measure has the inverse-element modular scalar. -/
theorem map_mul_left_invHaar (μ : Measure G) [IsHaarMeasure μ] [μ.Regular] (g : G) :
    Measure.map (g * ·) μ.inv = modularCharacter g⁻¹ • μ.inv := by
  have : (Measure.map (· * g⁻¹) μ).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g⁻¹)
  have hm : Measure.map (· * g⁻¹) μ = modularCharacter g⁻¹ • μ := by
    change Measure.map (· * g⁻¹) μ = modularCharacterFun g⁻¹ • μ
    rw [modularCharacterFun_eq_haarScalarFactor μ]
    exact isMulLeftInvariant_eq_smul_of_regular _ _
  have hc : (g * ·) ∘ (Inv.inv : G → G) =
      (Inv.inv : G → G) ∘ (· * g⁻¹) := by
    funext x
    simp
  rw [Measure.inv, Measure.map_map (measurable_const_mul g) measurable_inv, hc,
    ← Measure.map_map measurable_inv (measurable_mul_const _), hm,
    Measure.map_smul _ measurable_inv.aemeasurable]

omit H hH η [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  [IsFiniteMeasureOnCompacts η] [IsMulRightInvariant η] in
theorem integral_mul_left_invHaar (μ : Measure G) [IsHaarMeasure μ] [μ.Regular]
    (g : G) (f : G → ℝ) :
    (∫ x, f (g * x) ∂μ.inv) =
      (modularCharacter g⁻¹ : ℝ) * ∫ x, f x ∂μ.inv := by
  change (∫ x, f ((Homeomorph.mulLeft g).toMeasurableEquiv x) ∂μ.inv) = _
  rw [← integral_map_equiv (Homeomorph.mulLeft g).toMeasurableEquiv f]
  change (∫ x, f x ∂Measure.map (g * ·) μ.inv) = _
  rw [map_mul_left_invHaar, integral_smul_nnreal_measure]
  rfl

section Restriction

variable [H.Normal]
  [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

/-- Restriction of the ambient modular character to a closed normal subgroup. -/
theorem modularCharacter_normalSubgroup (h : H) :
    have : LocallyCompactSpace H := hH.locallyCompactSpace
    modularCharacter h = modularCharacter (h : G) := by
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let ν := normalQuotientRightHaar H
  let μH : Measure H := haar
  let ρ := rightQuotientLift H hH μH.inv ν
  have : IsMulRightInvariant ρ :=
    rightQuotientLift_rightInvariant H hH μH.inv ν (normalQuotientRightHaar_invariant H)
  have hρ0 : ρ ≠ 0 := rightQuotientLift_ne_zero H hH μH.inv ν
  have : NeZero ρ.inv := ⟨by
    intro hz
    apply hρ0
    calc
      ρ = ρ.inv.inv := (Measure.inv_inv ρ).symm
      _ = (0 : Measure G).inv := congrArg Measure.inv hz
      _ = 0 := by simp [Measure.inv_def]⟩
  have : IsHaarMeasure ρ.inv := {}
  obtain ⟨f, hf⟩ := exists_compact_integral_ne_zero ρ hρ0
  let f₁ : C_c(G, ℝ) :=
    f.comp (Homeomorph.mulLeft (h : G)⁻¹).toCocompactMap
  have havg : quotientAverageRealPositive H hH μH.inv f₁ =
      (modularCharacter h : ℝ) • quotientAverageRealPositive H hH μH.inv f := by
    ext q
    induction q using Quotient.inductionOn with
    | h x =>
      change (∫ k : H, f ((h : G)⁻¹ * (k.val * x)) ∂μH.inv) =
        (modularCharacter h : ℝ) * ∫ k : H, f (k.val * x) ∂μH.inv
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_inv] using
        integral_mul_left_invHaar μH h⁻¹ (fun k : H => f (k.val * x))
  have hi : (∫ x, f ((h : G)⁻¹ * x) ∂ρ) =
      (modularCharacter h : ℝ) * ∫ x, f x ∂ρ := by
    change (∫ x, f₁ x ∂ρ) = _
    rw [integral_rightQuotientLift, havg]
    change (∫ q, (modularCharacter h : ℝ) *
      quotientAverageRealPositive H hH μH.inv f q ∂ν) = _
    rw [integral_const_mul, integral_rightQuotientLift]
  have hg : (∫ x, f ((h : G)⁻¹ * x) ∂ρ) =
      (modularCharacter (h : G) : ℝ) * ∫ x, f x ∂ρ := by
    simpa only [Measure.inv_inv, inv_inv] using
      integral_mul_left_invHaar ρ.inv (h : G)⁻¹ f
  exact NNReal.coe_injective (mul_right_cancel₀ hf (hi.symm.trans hg))

end Restriction

end Langlands.QuotientIntegration

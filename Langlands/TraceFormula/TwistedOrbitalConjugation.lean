import Langlands.TraceFormula.TwistedOrbital

/-! # Conjugation on twisted orbital integrals -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.QuotientIntegration

variable {G : Type*} [Group G] {A : Type*} [FunLike A G G] [MonoidHomClass A G G]
variable (θ : A) (x δ : G)

theorem conj_mem_twistedCentralizer_iff (g : G) :
    x⁻¹ * g * x ∈ twistedCentralizer θ (twistedConj θ x δ) ↔
      g ∈ twistedCentralizer θ δ := by
  change twistedConj θ (x⁻¹ * g * x) (twistedConj θ x δ) = twistedConj θ x δ ↔
    twistedConj θ g δ = δ
  rw [twistedConj_mul, show x * (x⁻¹ * g * x) = g * x by group, ← twistedConj_mul]
  constructor
  · intro h
    have h' := congrArg (twistedConj θ x⁻¹) h
    simpa only [twistedConj_mul, mul_assoc, mul_inv_cancel, mul_one, twistedConj_one] using h'
  · intro h
    rw [h]

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation by `x⁻¹` identifies the stabilizers of the two twisted conjugates. -/
def twistedCentralizerConj :
    twistedCentralizer θ δ ≃ₜ* twistedCentralizer θ (twistedConj θ x δ) where
  toFun g := ⟨x⁻¹ * g.val * x, (conj_mem_twistedCentralizer_iff θ x δ g).2 g.property⟩
  invFun g := ⟨x * g.val * x⁻¹, (conj_mem_twistedCentralizer_iff θ x δ _).1
    (by
      rw [show x⁻¹ * (x * g.val * x⁻¹) * x = g.val by group]
      exact g.property)⟩
  left_inv g := Subtype.ext (by change x * (x⁻¹ * g.val * x) * x⁻¹ = g.val; group)
  right_inv g := Subtype.ext (by change x⁻¹ * (x * g.val * x⁻¹) * x = g.val; group)
  map_mul' g h := Subtype.ext (by change x⁻¹ * (g.val * h.val) * x =
    (x⁻¹ * g.val * x) * (x⁻¹ * h.val * x); group)
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp] theorem coe_twistedCentralizerConj (g : twistedCentralizer θ δ) :
    (twistedCentralizerConj θ x δ g).val = x⁻¹ * g.val * x := rfl

/-- Left translation by `x⁻¹` identifies the two orbit parameter spaces. -/
def twistedQuotientConj :
    LeftQuotient (twistedCentralizer θ δ) ≃ₜ
      LeftQuotient (twistedCentralizer θ (twistedConj θ x δ)) :=
  Homeomorph.Quotient.congr (Homeomorph.mulLeft x⁻¹) (by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change b * a⁻¹ ∈ twistedCentralizer θ δ ↔
      (x⁻¹ * b) * (x⁻¹ * a)⁻¹ ∈ twistedCentralizer θ (twistedConj θ x δ)
    rw [show (x⁻¹ * b) * (x⁻¹ * a)⁻¹ = x⁻¹ * (b * a⁻¹) * x by group,
      conj_mem_twistedCentralizer_iff])

@[simp] theorem twistedQuotientConj_mk (g : G) :
    twistedQuotientConj θ x δ (Quotient.mk _ g) = Quotient.mk _ (x⁻¹ * g) := rfl

end Topology

section Measure

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
variable [MeasurableMul G]
variable [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
variable [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
variable [MeasurableSpace (LeftQuotient (twistedCentralizer θ (twistedConj θ x δ)))]
variable [BorelSpace (LeftQuotient (twistedCentralizer θ (twistedConj θ x δ)))]

variable (μ : Measure (twistedCentralizer θ δ)) [μ.IsMulRightInvariant]

instance map_twistedCentralizerConj_isMulRightInvariant :
    (Measure.map (twistedCentralizerConj θ x δ) μ).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    let e := twistedCentralizerConj θ x δ
    have he : Measurable (e : _ → _) := e.continuous.measurable
    change Measure.map (· * g) (Measure.map e μ) = Measure.map e μ
    rw [Measure.map_map (measurable_mul_const g) he]
    have heq : (· * g) ∘ e = e ∘ (· * e.symm g) := by
      funext c
      simp only [Function.comp_apply, map_mul, e.apply_symm_apply]
    rw [heq, ← Measure.map_map he (measurable_mul_const _),
      map_mul_right_eq_self]

omit [MeasurableMul G]
  [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ δ))]
  [MeasurableSpace (LeftQuotient (twistedCentralizer θ (twistedConj θ x δ)))]
  [BorelSpace (LeftQuotient (twistedCentralizer θ (twistedConj θ x δ)))] in
theorem quotientAverage_twistedQuotientConj
    (f : G → ℂ) (q : LeftQuotient (twistedCentralizer θ δ)) :
    quotientAverage (twistedCentralizer θ (twistedConj θ x δ))
      (Measure.map (twistedCentralizerConj θ x δ) μ) f (twistedQuotientConj θ x δ q) =
      quotientAverage (twistedCentralizer θ δ) μ (fun g => f (x⁻¹ * g)) q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [twistedQuotientConj_mk, quotientAverage_mk, quotientAverage_mk]
    let e := (twistedCentralizerConj θ x δ).toHomeomorph.toMeasurableEquiv
    change (∫ h, f (h.val * (x⁻¹ * g)) ∂Measure.map e μ) = _
    rw [integral_map_equiv e]
    change (∫ h : twistedCentralizer θ δ, f ((x⁻¹ * h.val * x) * (x⁻¹ * g)) ∂μ) = _
    simp only [mul_assoc, mul_inv_cancel_left]

/-- Quotient compatibility is preserved by this transport for a left-invariant
ambient measure and a right-invariant stabilizer measure. -/
theorem isCompatible_twistedQuotientConj (μG : Measure G) [μG.IsMulLeftInvariant]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (hν : IsCompatible (twistedCentralizer θ δ) μG μ ν) :
    IsCompatible (twistedCentralizer θ (twistedConj θ x δ)) μG
      (Measure.map (twistedCentralizerConj θ x δ) μ)
      (Measure.map (twistedQuotientConj θ x δ) ν) where
  nonzero := (Measure.map_ne_zero_iff
    (twistedQuotientConj θ x δ).continuous.measurable.aemeasurable).2 hν.nonzero
  regular := by
    have := hν.regular
    exact Measure.Regular.map (twistedQuotientConj θ x δ)
  right_invariant g := by
    let e := twistedQuotientConj θ x δ
    let r := rightTranslate (twistedCentralizer θ δ) g
    let r' := rightTranslate (twistedCentralizer θ (twistedConj θ x δ)) g
    refine ⟨r'.continuous.measurable, ?_⟩
    change Measure.map r' (Measure.map e ν) = Measure.map e ν
    have he : r' ∘ e = e ∘ r := by
      funext q
      induction q using Quotient.inductionOn with
      | h a =>
        dsimp only [e, r, r', Function.comp_apply]
        simp only [twistedQuotientConj_mk, rightTranslate_mk, mul_assoc]
    rw [Measure.map_map r'.continuous.measurable e.continuous.measurable, he,
      ← Measure.map_map e.continuous.measurable r.continuous.measurable,
      (hν.right_invariant g).map_eq]
  averaging_integrable f hf hc := by
    apply (integrable_map_equiv (twistedQuotientConj θ x δ).toMeasurableEquiv _).2
    change Integrable (fun q => quotientAverage _
      (Measure.map (twistedCentralizerConj θ x δ) μ) f (twistedQuotientConj θ x δ q)) ν
    simpa only [quotientAverage_twistedQuotientConj] using
      hν.averaging_integrable (fun a => f (x⁻¹ * a)) (hf.comp (continuous_const.mul continuous_id))
        (hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  integral_formula f hf hc := by
    let e := (twistedQuotientConj θ x δ).toMeasurableEquiv
    change (∫ q, quotientAverage _ (Measure.map (twistedCentralizerConj θ x δ) μ) f q
        ∂Measure.map e ν) = _
    rw [integral_map_equiv e]
    change (∫ q, quotientAverage _ (Measure.map (twistedCentralizerConj θ x δ) μ) f
        (twistedQuotientConj θ x δ q) ∂ν) = _
    simp only [quotientAverage_twistedQuotientConj]
    rw [hν.integral_formula (fun a => f (x⁻¹ * a)) (hf.comp (continuous_const.mul continuous_id))
      (hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹))]
    exact (measurePreserving_mul_left μG x⁻¹).integral_comp
      (Homeomorph.mulLeft x⁻¹).toMeasurableEquiv.measurableEmbedding f

omit [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] in
/-- Changing representatives and transporting the quotient measure preserve
the twisted orbital integral of the same test function. -/
theorem twistedOrbitalIntegral_twistedQuotientConj
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : G → ℂ) :
    twistedOrbitalIntegral θ (twistedConj θ x δ)
      (Measure.map (twistedQuotientConj θ x δ) ν) f = twistedOrbitalIntegral θ δ ν f := by
  unfold twistedOrbitalIntegral
  let e := (twistedQuotientConj θ x δ).toMeasurableEquiv
  change (∫ q, twistedOrbitFunction θ (twistedConj θ x δ) f q ∂Measure.map e ν) = _
  rw [integral_map_equiv e]
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change twistedOrbitFunction θ (twistedConj θ x δ) f (twistedQuotientConj θ x δ
      (Quotient.mk _ g)) = twistedOrbitFunction θ δ f (Quotient.mk _ g)
    simp only [twistedQuotientConj_mk, twistedOrbitFunction_mk]
    congr 1
    change twistedConj θ (x⁻¹ * g) (twistedConj θ x δ) = twistedConj θ g δ
    rw [twistedConj_mul, mul_inv_cancel_left]

end Measure

end Langlands.TraceFormula

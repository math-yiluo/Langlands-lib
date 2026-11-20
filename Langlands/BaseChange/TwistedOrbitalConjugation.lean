import Langlands.Analysis.Local.QuotientMeasureEquiv
import Langlands.BaseChange.OrbitalIntegral
import Mathlib.MeasureTheory.Group.Integral

/-! Compatible quotient measures and orbital integrals under twisted conjugation. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure
open Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

variable {G : Type u} [Group G]

private theorem mem_twistedCentralizer_conj_iff (θ : G →* G) (δ x h : G) :
    x⁻¹ * h * x ∈ twistedCentralizer θ (twistedConj θ x δ) ↔
      h ∈ twistedCentralizer θ δ := by
  change twistedConj θ (x⁻¹ * h * x) (twistedConj θ x δ) =
    twistedConj θ x δ ↔ twistedConj θ h δ = δ
  rw [twistedConj_mul, show x * (x⁻¹ * h * x) = h * x by group, ← twistedConj_mul]
  have hinj : Function.Injective (twistedConj θ x) := by
    apply Function.LeftInverse.injective (g := twistedConj θ x⁻¹)
    intro y
    rw [twistedConj_mul, mul_inv_cancel, twistedConj_one]
  exact hinj.eq_iff

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (θ : G →* G) (δ x : G)

/-- Conjugation by `x⁻¹` identifies the two twisted centralizers. -/
def twistedCentralizerConj :
    twistedCentralizer θ δ ≃ₜ* twistedCentralizer θ (twistedConj θ x δ) :=
  let e : G ≃ₜ* G :=
    { toMulEquiv := MulAut.conj x⁻¹
      continuous_toFun := IsTopologicalGroup.continuous_conj _
      continuous_invFun := by
        change Continuous (fun h : G => x⁻¹⁻¹ * h * x⁻¹)
        rw [inv_inv]
        exact IsTopologicalGroup.continuous_conj x }
  subgroupContinuousMulEquiv e (twistedCentralizer θ δ)
    (twistedCentralizer θ (twistedConj θ x δ)) (fun h => by
    simpa [e] using mem_twistedCentralizer_conj_iff θ δ x h)

@[simp] theorem twistedCentralizerConj_apply_coe (h : twistedCentralizer θ δ) :
    (↑(twistedCentralizerConj θ δ x h) : G) = x⁻¹ * h.val * x := by
  change x⁻¹ * h.val * x⁻¹⁻¹ = x⁻¹ * h.val * x
  rw [inv_inv]

/-- Left translation by `x⁻¹` identifies the two orbit quotients. -/
def twistedOrbitQuotientConj : LeftQuotient (twistedCentralizer θ δ) ≃ₜ
    LeftQuotient (twistedCentralizer θ (twistedConj θ x δ)) :=
  Homeomorph.Quotient.congr (Homeomorph.mulLeft x⁻¹) (by
    intro a b
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change b * a⁻¹ ∈ twistedCentralizer θ δ ↔
      (x⁻¹ * b) * (x⁻¹ * a)⁻¹ ∈ twistedCentralizer θ (twistedConj θ x δ)
    rw [show (x⁻¹ * b) * (x⁻¹ * a)⁻¹ = x⁻¹ * (b * a⁻¹) * x by group]
    exact (mem_twistedCentralizer_conj_iff θ δ x (b * a⁻¹)).symm)

@[simp] theorem twistedOrbitQuotientConj_mk (a : G) :
    twistedOrbitQuotientConj θ δ x (Quotient.mk _ a) = Quotient.mk _ (x⁻¹ * a) := rfl

private theorem twistedOrbitFunction_conj (f : G → ℂ) (q : LeftQuotient (twistedCentralizer θ δ)) :
    twistedOrbitFunction θ (twistedConj θ x δ) f (twistedOrbitQuotientConj θ δ x q) =
      twistedOrbitFunction θ δ f q := by
  induction q using Quotient.inductionOn with
  | h a =>
    change f (twistedConj θ (x⁻¹ * a) (twistedConj θ x δ)) = f (twistedConj θ a δ)
    rw [twistedConj_mul, mul_inv_cancel_left]

section Compatible

variable [MeasurableSpace G] [BorelSpace G]
variable (μH : Measure (twistedCentralizer θ δ)) [IsMulRightInvariant μH]
variable (μK : Measure (twistedCentralizer θ (twistedConj θ x δ))) [IsMulRightInvariant μK]

private theorem quotientAverage_twistedConj
    (hμK : μK = Measure.map (twistedCentralizerConj θ δ x) μH)
    (f : G → ℂ) (q : LeftQuotient (twistedCentralizer θ δ)) :
    quotientAverage (twistedCentralizer θ (twistedConj θ x δ)) μK f (twistedOrbitQuotientConj θ δ x q) =
      quotientAverage (twistedCentralizer θ δ) μH (fun a => f (x⁻¹ * a)) q := by
  induction q using Quotient.inductionOn with
  | h a =>
    rw [twistedOrbitQuotientConj_mk, quotientAverage_mk, quotientAverage_mk, hμK]
    calc
      (∫ h, f (h.val * (x⁻¹ * a)) ∂Measure.map (twistedCentralizerConj θ δ x) μH) =
          ∫ h, f (↑(twistedCentralizerConj θ δ x h) * (x⁻¹ * a)) ∂μH :=
        integral_map_equiv (twistedCentralizerConj θ δ x).toHomeomorph.toMeasurableEquiv _
      _ = _ := by
        simp only [twistedCentralizerConj_apply_coe, mul_assoc, mul_inv_cancel_left]

/-- Left translation in the ambient group gives the Weil formula for the
transported centralizer and orbit quotient measures. -/
theorem isCompatible_map_twistedConj (μ : Measure G) [IsMulLeftInvariant μ]
    (hμK : μK = Measure.map (twistedCentralizerConj θ δ x) μH)
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (hν : IsCompatible (twistedCentralizer θ δ) μ μH ν) :
    IsCompatible (twistedCentralizer θ (twistedConj θ x δ)) μ μK
      (Measure.map (twistedOrbitQuotientConj θ δ x) ν) where
  nonzero := (Measure.map_ne_zero_iff
    (twistedOrbitQuotientConj θ δ x).continuous.measurable.aemeasurable).2 hν.nonzero
  regular := by
    let := hν.regular
    exact Measure.Regular.map (twistedOrbitQuotientConj θ δ x)
  right_invariant g := by
    let e := twistedOrbitQuotientConj θ δ x
    let source := rightTranslate (twistedCentralizer θ δ) g
    let target := rightTranslate (twistedCentralizer θ (twistedConj θ x δ)) g
    refine ⟨target.continuous.measurable, ?_⟩
    have hcomm : target ∘ e = e ∘ source := by
      funext q
      induction q using Quotient.inductionOn with
      | h a =>
        simp only [e, source, target, Function.comp_apply, rightTranslate_mk,
          twistedOrbitQuotientConj_mk, mul_assoc]
    change Measure.map target (Measure.map e ν) = Measure.map e ν
    rw [Measure.map_map target.continuous.measurable e.continuous.measurable,
      hcomm, ← Measure.map_map e.continuous.measurable source.continuous.measurable]
    exact congrArg (Measure.map e) (hν.right_invariant g).map_eq
  averaging_integrable f hf hfc := by
    apply (integrable_map_equiv (twistedOrbitQuotientConj θ δ x).toMeasurableEquiv _).2
    change Integrable (fun q => quotientAverage _ μK f (twistedOrbitQuotientConj θ δ x q)) ν
    simp_rw [quotientAverage_twistedConj θ δ x μH μK hμK]
    exact hν.averaging_integrable (fun a => f (x⁻¹ * a))
      (hf.comp (Homeomorph.mulLeft x⁻¹).continuous)
      (hfc.comp_isClosedEmbedding (Homeomorph.mulLeft x⁻¹).isClosedEmbedding)
  integral_formula f hf hfc := by
    let e := twistedOrbitQuotientConj θ δ x
    calc
      (∫ q, quotientAverage _ μK f q ∂Measure.map e ν) =
          ∫ q, quotientAverage _ μK f (e q) ∂ν := integral_map_equiv e.toMeasurableEquiv _
      _ = ∫ q, quotientAverage _ μH (fun a => f (x⁻¹ * a)) q ∂ν := by
        simp_rw [e, quotientAverage_twistedConj θ δ x μH μK hμK]
      _ = ∫ a, f (x⁻¹ * a) ∂μ :=
        hν.integral_formula (fun a => f (x⁻¹ * a))
          (hf.comp (Homeomorph.mulLeft x⁻¹).continuous)
          (hfc.comp_isClosedEmbedding (Homeomorph.mulLeft x⁻¹).isClosedEmbedding)
      _ = ∫ a, f a ∂μ := integral_mul_left_eq_self f x⁻¹

end Compatible

/-- Twisted conjugation with quotient measure transport preserves integrability
of the orbital integrand and the orbital integral. -/
theorem twistedOrbitalIntegral_map_conj
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) (f : G → ℂ) :
    let ν' := Measure.map (twistedOrbitQuotientConj θ δ x) ν
    (Integrable (twistedOrbitFunction θ (twistedConj θ x δ) f) ν' ↔
      Integrable (twistedOrbitFunction θ δ f) ν) ∧
    twistedOrbitalIntegral θ (twistedConj θ x δ) ν' f = twistedOrbitalIntegral θ δ ν f := by
  let e := (twistedOrbitQuotientConj θ δ x).toMeasurableEquiv
  have hfun : twistedOrbitFunction θ (twistedConj θ x δ) f ∘ e =
      twistedOrbitFunction θ δ f := funext (twistedOrbitFunction_conj θ δ x f)
  constructor
  · change Integrable _ (Measure.map e ν) ↔ _
    rw [integrable_map_equiv, hfun]
  · change (∫ q, twistedOrbitFunction θ (twistedConj θ x δ) f q ∂Measure.map e ν) = _
    exact (integral_map_equiv e _).trans (congrArg (fun g => ∫ q, g q ∂ν) hfun)

/-- Compatibility and orbital integrals are preserved by simultaneous transport of
the centralizer measure by conjugation and the quotient measure by left translation. -/
abbrev TwistedOrbitalConjugationStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) (δ x : G) (μ : Measure G) [IsMulLeftInvariant μ],
    let H := twistedCentralizer θ δ
    let K := twistedCentralizer θ (twistedConj θ x δ)
    ∀ (μH : Measure H) [IsMulRightInvariant μH] (μK : Measure K) [IsMulRightInvariant μK],
      μK = Measure.map (twistedCentralizerConj θ δ x) μH →
      ∀ (ν : Measure (LeftQuotient H)), IsCompatible H μ μH ν →
        let ν' := Measure.map (twistedOrbitQuotientConj θ δ x) ν
        IsCompatible K μ μK ν' ∧ ∀ f : G → ℂ,
          (Integrable (twistedOrbitFunction θ (twistedConj θ x δ) f) ν' ↔
            Integrable (twistedOrbitFunction θ δ f) ν) ∧
          twistedOrbitalIntegral θ (twistedConj θ x δ) ν' f = twistedOrbitalIntegral θ δ ν f

theorem twistedOrbitalConjugation : TwistedOrbitalConjugationStatement.{u} := by
  intro G _ _ _ _ _ θ δ x μ _ H K μH _ μK _ hμK ν hν
  exact ⟨isCompatible_map_twistedConj θ δ x μH μK μ hμK ν hν,
    twistedOrbitalIntegral_map_conj θ δ x ν⟩

end Langlands.BaseChange

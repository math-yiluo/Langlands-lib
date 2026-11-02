import Langlands.Global.LeftCosetSpace
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measures on left homogeneous quotients

Construct quotient measures from a supplied fundamental domain for the left
subgroup action. Countability, invariance and all convergence inputs are explicit.
-/

noncomputable section

universe u v

open MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] (Γ : Subgroup H) [MeasurableSpace H]

theorem measurable_mk : Measurable (mk Γ) := measurable_quotient_mk''

/-- Push forward the restriction of the ambient measure to a set of representatives. -/
def quotientMeasure (ν : Measure H) (s : Set H) : Measure (Langlands.Global.LeftCosetSpace Γ) :=
  Measure.map (mk Γ) (ν.restrict s)

theorem quotientMeasure_apply (ν : Measure H) (s : Set H)
    {A : Set (Langlands.Global.LeftCosetSpace Γ)} (hA : MeasurableSet A) :
    quotientMeasure Γ ν s A = ν ((mk Γ ⁻¹' A) ∩ s) := by
  rw [quotientMeasure, Measure.map_apply (measurable_mk Γ) hA,
    Measure.restrict_apply ((measurable_mk Γ) hA)]

@[simp]
theorem quotientMeasure_univ (ν : Measure H) (s : Set H) :
    quotientMeasure Γ ν s univ = ν s := by
  rw [quotientMeasure_apply Γ ν s MeasurableSet.univ]
  simp

theorem measurePreserving_mk (ν : Measure H) (s : Set H) :
    MeasurePreserving (mk Γ) (ν.restrict s) (quotientMeasure Γ ν s) :=
  ⟨measurable_mk Γ, rfl⟩

theorem quotientMeasure_smul (ν : Measure H) (s : Set H) (c : ℝ≥0∞) :
    quotientMeasure Γ (c • ν) s = c • quotientMeasure Γ ν s := by
  simp only [quotientMeasure, Measure.restrict_smul,
    Measure.map_smul _ (measurable_mk Γ).aemeasurable]

/-- Unit-mass normalization; its probability law requires positive finite mass. -/
def normalizedMeasure (ν : Measure H) (s : Set H) :
    Measure (Langlands.Global.LeftCosetSpace Γ) :=
  (ν s)⁻¹ • quotientMeasure Γ ν s

theorem normalizedMeasure_univ (ν : Measure H) (s : Set H)
    (hzero : ν s ≠ 0) (hfinite : ν s ≠ ⊤) :
    normalizedMeasure Γ ν s univ = 1 := by
  simp only [normalizedMeasure, Measure.smul_apply, smul_eq_mul, quotientMeasure_univ]
  exact ENNReal.inv_mul_cancel hzero hfinite

theorem isProbabilityMeasure_normalizedMeasure (ν : Measure H) (s : Set H)
    (hzero : ν s ≠ 0) (hfinite : ν s ≠ ⊤) :
    IsProbabilityMeasure (normalizedMeasure Γ ν s) :=
  ⟨normalizedMeasure_univ Γ ν s hzero hfinite⟩

theorem isFiniteMeasure_quotientMeasure (ν : Measure H) (s : Set H)
    (hfinite : ν s ≠ ⊤) : IsFiniteMeasure (quotientMeasure Γ ν s) :=
  ⟨by simpa using hfinite.lt_top⟩

section Integration

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_quotientMeasure (ν : Measure H) (s : Set H)
    (f : Langlands.Global.LeftCosetSpace Γ → E)
    (hf : AEStronglyMeasurable f (quotientMeasure Γ ν s)) :
    ∫ q, f q ∂quotientMeasure Γ ν s = ∫ x in s, f (mk Γ x) ∂ν :=
  integral_map (measurable_mk Γ).aemeasurable hf

omit [NormedSpace ℝ E] in
theorem integrable_quotientMeasure_iff (ν : Measure H) (s : Set H)
    (f : Langlands.Global.LeftCosetSpace Γ → E)
    (hf : AEStronglyMeasurable f (quotientMeasure Γ ν s)) :
    Integrable f (quotientMeasure Γ ν s) ↔ IntegrableOn (fun x => f (mk Γ x)) s ν :=
  integrable_map_measure hf (measurable_mk Γ).aemeasurable

end Integration

section FundamentalDomain

variable [Countable Γ] [MeasurableConstSMul Γ H]
  (ν : Measure H) [SMulInvariantMeasure Γ H ν]
  {s t : Set H} (hs : IsFundamentalDomain Γ s ν)

include hs

theorem quotientMeasure_eq (ht : IsFundamentalDomain Γ t ν) :
    quotientMeasure Γ ν s = quotientMeasure Γ ν t :=
  hs.quotientMeasure_eq ν ht

theorem quotientMeasure_compatible :
    QuotientMeasureEqMeasurePreimage ν (quotientMeasure Γ ν s) :=
  hs.quotientMeasureEqMeasurePreimage_quotientMeasure

theorem normalizedMeasure_eq (ht : IsFundamentalDomain Γ t ν) :
    normalizedMeasure Γ ν s = normalizedMeasure Γ ν t := by
  have hm : ν s = ν t := by
    simpa using congrArg (fun μ : Measure (Langlands.Global.LeftCosetSpace Γ) => μ univ)
      (quotientMeasure_eq Γ ν hs ht)
  rw [normalizedMeasure, normalizedMeasure, hm, quotientMeasure_eq Γ ν hs ht]

end FundamentalDomain

section Translation

variable [MeasurableMul H]

theorem measurable_rightTranslate (g : H) : Measurable (rightTranslate Γ g) :=
  measurable_from_quotient.mpr ((measurable_mk Γ).comp (measurable_id.mul_const g))

variable [Countable Γ] (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
  {s : Set H} (hs : IsFundamentalDomain Γ s ν)

include hs

theorem measurePreserving_rightTranslate (g : H) :
    MeasurePreserving (rightTranslate Γ g) (quotientMeasure Γ ν s)
      (quotientMeasure Γ ν s) := by
  refine ⟨measurable_rightTranslate Γ g, ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_rightTranslate Γ g) hA,
    quotientMeasure_apply Γ ν s ((measurable_rightTranslate Γ g) hA)]
  have hsg : IsFundamentalDomain Γ (MulOpposite.op g • s) ν := hs.smul_of_comm _
  rw [quotientMeasure_eq Γ ν hs hsg, quotientMeasure_apply Γ ν _ hA]
  have hpre :
      mk Γ ⁻¹' (rightTranslate Γ g ⁻¹' A) ∩ s =
        (fun x : H => x * g) ⁻¹' ((mk Γ ⁻¹' A) ∩ (MulOpposite.op g • s)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, rightTranslate_mk, mem_smul_set_iff_inv_smul_mem,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv, MulOpposite.unop_op,
      mul_inv_cancel_right]
  rw [hpre, measure_preimage_mul_right]

theorem smulInvariant_quotientMeasure :
    SMulInvariantMeasure Hᵐᵒᵖ (Langlands.Global.LeftCosetSpace Γ) (quotientMeasure Γ ν s) where
  measure_preimage_smul g A hA := by
    exact (measurePreserving_rightTranslate Γ ν hs (MulOpposite.unop g)).measure_preimage
      hA.nullMeasurableSet

theorem measurePreserving_rightTranslate_normalized (g : H) :
    MeasurePreserving (rightTranslate Γ g) (normalizedMeasure Γ ν s)
      (normalizedMeasure Γ ν s) := by
  refine ⟨measurable_rightTranslate Γ g, ?_⟩
  rw [normalizedMeasure, Measure.map_smul _ (measurable_rightTranslate Γ g).aemeasurable,
    (measurePreserving_rightTranslate Γ ν hs g).map_eq]

end Translation

section Unfolding

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The left-subgroup orbit sum. Summability remains a separate assertion. -/
abbrev automorphize (f : H → E) : Langlands.Global.LeftCosetSpace Γ → E :=
  MulAction.automorphize (α := Γ) f

omit [MeasurableSpace H] [NormedSpace ℝ E] in
@[simp]
theorem automorphize_mk (f : H → E) (x : H) :
    automorphize Γ f (mk Γ x) = ∑' γ : Γ, f ((γ : H) * x) := rfl

variable [Countable Γ] [MeasurableConstSMul Γ H]
  (ν : Measure H) [SMulInvariantMeasure Γ H ν]
  {s : Set H} (hs : IsFundamentalDomain Γ s ν)

include hs

theorem integral_eq_integral_automorphize {f : H → E}
    (hf : Integrable f ν)
    (ha : AEStronglyMeasurable (automorphize Γ f) (quotientMeasure Γ ν s)) :
    ∫ x, f x ∂ν = ∫ q, automorphize Γ f q ∂quotientMeasure Γ ν s := by
  calc
    ∫ x, f x ∂ν = ∑' γ : Γ, ∫ x in s, f (γ • x) ∂ν :=
      hs.integral_eq_tsum'' f hf
    _ = ∫ x in s, ∑' γ : Γ, f (γ • x) ∂ν := by
      rw [integral_tsum]
      · exact fun γ => (hf.1.comp_quasiMeasurePreserving
          (measurePreserving_smul γ ν).quasiMeasurePreserving).restrict
      · rw [← hs.lintegral_eq_tsum'' (‖f ·‖ₑ)]
        exact ne_of_lt hf.2
    _ = ∫ q, automorphize Γ f q ∂quotientMeasure Γ ν s :=
      (integral_quotientMeasure Γ ν s _ ha).symm

end Unfolding

section Borel

variable [TopologicalSpace H] [PolishSpace H] [BorelSpace H]
  [T0Space (Langlands.Global.LeftCosetSpace Γ)]
  [SecondCountableTopology (Langlands.Global.LeftCosetSpace Γ)]

theorem quotient_borelSpace : BorelSpace (Langlands.Global.LeftCosetSpace Γ) :=
  Quotient.borelSpace

end Borel

end Langlands.Global.LeftCosetSpace

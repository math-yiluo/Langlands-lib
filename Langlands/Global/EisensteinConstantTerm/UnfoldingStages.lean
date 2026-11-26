import Langlands.Analysis.Local.QuotientWeilKernel
import Langlands.Global.LeftCosetSubgroupSlice
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Integrating over a discrete quotient in stages through a closed subgroup -/

noncomputable section

universe u v

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open Langlands.QuotientIntegration

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant] [μH.IsMulLeftInvariant]

section Slice

variable (Δ : Subgroup G) (hΔH : Δ ≤ H) [Countable (Δ.comap H.subtype)]
  {D : Set G} (hD : MeasurableSet D) (hDu : ∀ g : G, ∃! γ : Δ, (γ : G) * g ∈ D)
  {t : Set H} (ht : IsFundamentalDomain (Δ.comap H.subtype) t μH)

include hΔH hD hDu ht in
/-- On one orbit, the indicator of a transversal of `Δ ≤ H` integrates a left
`Δ`-invariant function like a fundamental domain of `Δ` in `H`. -/
theorem lintegral_orbitKernel_indicator (f : G → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ γ ∈ Δ, ∀ g, f (γ * g) = f g) (g : G) :
    ∫⁻ x, D.indicator f x ∂orbitKernel H hH μH (Quotient.mk _ g) =
      ∫⁻ a in t, f (a.val * g) ∂μH := by
  rw [orbitKernel_mk, lintegral_map (hfm.indicator hD)
    (continuous_subtype_val.mul_const g).measurable]
  have heq : (fun a : H => D.indicator f (a.val * g)) =
      (subgroupSlice H D g).indicator (fun a : H => f (a.val * g)) := by
    funext a
    by_cases ha : a.val * g ∈ D
    · rw [indicator_of_mem ha, indicator_of_mem (show a ∈ subgroupSlice H D g from ha)]
    · rw [indicator_of_notMem ha,
        indicator_of_notMem (show a ∉ subgroupSlice H D g from ha)]
  rw [show (∫⁻ a : H, D.indicator f (a.val * g) ∂μH) =
      ∫⁻ a in subgroupSlice H D g, f (a.val * g) ∂μH from
    (lintegral_congr fun a => congrFun heq a).trans
      (lintegral_indicator (measurableSet_subgroupSlice H hD g) _)]
  refine (isFundamentalDomain_subgroupSlice Δ H hΔH hD hDu g μH).setLIntegral_eq ht _ ?_
  intro δ a
  change f (((δ : H) * a : H).val * g) = f (a.val * g)
  rw [Subgroup.coe_mul, mul_assoc]
  exact hf _ δ.property _

include hΔH hD hDu ht in
/-- The Bochner form of `lintegral_orbitKernel_indicator`. -/
theorem integral_orbitKernel_indicator {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G → E) (hfm : StronglyMeasurable f)
    (hf : ∀ γ ∈ Δ, ∀ g, f (γ * g) = f g) (g : G) :
    ∫ x, D.indicator f x ∂orbitKernel H hH μH (Quotient.mk _ g) =
      ∫ a in t, f (a.val * g) ∂μH := by
  rw [orbitKernel_mk, integral_map (continuous_subtype_val.mul_const g).measurable.aemeasurable
    (hfm.indicator hD).aestronglyMeasurable]
  have heq : (fun a : H => D.indicator f (a.val * g)) =
      (subgroupSlice H D g).indicator (fun a : H => f (a.val * g)) := by
    funext a
    by_cases ha : a.val * g ∈ D
    · rw [indicator_of_mem ha, indicator_of_mem (show a ∈ subgroupSlice H D g from ha)]
    · rw [indicator_of_notMem ha,
        indicator_of_notMem (show a ∉ subgroupSlice H D g from ha)]
  rw [show (∫ a : H, D.indicator f (a.val * g) ∂μH) =
      ∫ a in subgroupSlice H D g, f (a.val * g) ∂μH from
    (integral_congr_ae (Filter.Eventually.of_forall fun a => congrFun heq a)).trans
      (integral_indicator (measurableSet_subgroupSlice H hD g))]
  refine (isFundamentalDomain_subgroupSlice Δ H hΔH hD hDu g μH).setIntegral_eq ht ?_
  intro δ a
  change f (((δ : H) * a : H).val * g) = f (a.val * g)
  rw [Subgroup.coe_mul, mul_assoc]
  exact hf _ δ.property _

end Slice

section Stages

variable [IsFiniteMeasureOnCompacts μH]
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
  (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μG μH ν)
  (Δ : Subgroup G) (hΔH : Δ ≤ H) [Countable (Δ.comap H.subtype)]
  {D : Set G} (hD : MeasurableSet D) (hDu : ∀ g : G, ∃! γ : Δ, (γ : G) * g ∈ D)
  {t : Set H} (ht : IsFundamentalDomain (Δ.comap H.subtype) t μH)

include hH hν hΔH hD hDu ht in
/-- **Stages, nonnegative form.** For a transversal `D` of a discrete `Δ ≤ H`, a fundamental
domain `t` of `Δ` in `H` and a compatible quotient measure `ν` on `H \ G`, the integral over `D`
of a left `Δ`-invariant function is the `ν`-integral of its integrals over the `t`-slices of the
`H`-orbits. -/
theorem lintegral_transversal_eq (f : G → ℝ≥0∞) (hfm : Measurable f)
    (hf : ∀ γ ∈ Δ, ∀ g, f (γ * g) = f g) :
    ∫⁻ x in D, f x ∂μG = ∫⁻ q, ∫⁻ a in t, f (a.val * Quotient.out q) ∂μH ∂ν := by
  rw [← lintegral_indicator hD, ← lintegral_orbitKernel H hH μH μG ν hν _ (hfm.indicator hD)]
  refine lintegral_congr fun q => ?_
  conv_lhs => rw [← Quotient.out_eq q]
  exact lintegral_orbitKernel_indicator H hH μH Δ hΔH hD hDu ht f hfm hf _

include hH hν hΔH hD hDu ht in
/-- **Stages, Bochner form.** Under the hypotheses of `lintegral_transversal_eq`, a left
`Δ`-invariant function integrable on `D` has `ν`-integrable slice integrals, and its integral over
`D` is their `ν`-integral. -/
theorem integral_transversal_eq {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G → E) (hfm : StronglyMeasurable f)
    (hf : ∀ γ ∈ Δ, ∀ g, f (γ * g) = f g) (hint : IntegrableOn f D μG) :
    Integrable (fun q => ∫ a in t, f (a.val * Quotient.out q) ∂μH) ν ∧
      ∫ x in D, f x ∂μG = ∫ q, ∫ a in t, f (a.val * Quotient.out q) ∂μH ∂ν := by
  let κ := orbitKernel H hH μH
  have hcomp : κ ∘ₘ ν = μG := orbitKernel_comp H hH μH μG ν hν
  have hI : Integrable (D.indicator f) μG := (integrable_indicator_iff hD).mpr hint
  have hslice : ∀ q, ∫ x, D.indicator f x ∂κ q = ∫ a in t, f (a.val * Quotient.out q) ∂μH := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    exact integral_orbitKernel_indicator H hH μH Δ hΔH hD hDu ht f hfm hf _
  have hI' : Integrable (D.indicator f) ((κ ∘ₖ Kernel.const Unit ν) ()) := by
    rw [← Measure.comp_eq_comp_const_apply, hcomp]
    exact hI
  have hint' := hI'.integral_comp
  have heq := Kernel.integral_comp hI'
  rw [← Measure.comp_eq_comp_const_apply, hcomp, Kernel.const_apply] at heq
  rw [Kernel.const_apply] at hint'
  refine ⟨?_, ?_⟩
  · simpa only [hslice] using hint'
  · rw [← integral_indicator hD, heq]
    exact integral_congr_ae (Filter.Eventually.of_forall hslice)

end Stages

end Langlands.Global.LeftCosetSpace

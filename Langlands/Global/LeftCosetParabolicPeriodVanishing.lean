import Langlands.Global.LeftCosetSemidirectPeriod
import Langlands.Global.LeftCosetSubgroupSlice
import Langlands.Analysis.Local.QuotientWeilKernel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Vanishing periods on a discrete quotient from the radical periods -/

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Set TopologicalSpace Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open Langlands.QuotientIntegration

section ClosedSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Γ H : Subgroup G} [BorelSpace H] [BorelSpace (LeftCosetSpace H)]

local instance : SecondCountableTopology H := secondCountableTopology_induced _ G Subtype.val

/-- If every right translate has zero period on the discrete quotient inside
a closed subgroup, its integrable ambient period also vanishes. -/
def ClosedSubgroupPeriodVanishingStatement [T2Space G] [LocallyCompactSpace G]
    (_hle : Γ ≤ H) (hΓ : IsDiscrete (Γ : Set G)) (_hH : IsClosed (H : Set G))
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (μH : Measure H) [SFinite μH] [IsFiniteMeasureOnCompacts μH]
    [μH.IsMulLeftInvariant] [μH.IsMulRightInvariant]
    (ν : Measure (LeftCosetSpace H)) : Prop :=
  IsCompatible H μG μH ν →
    ∀ f : G → ℂ, Measurable f → (∀ γ : Γ, ∀ g, f (γ.val * g) = f g) →
      IntegrableOn f (fundamentalDomain Γ hΓ) μG →
      (∀ g : G, ∫ h in fundamentalDomain (Γ.comap H.subtype)
          (hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective),
          f (h.val * g) ∂μH = 0) →
      ∫ g in fundamentalDomain Γ hΓ, f g ∂μG = 0

theorem closedSubgroupPeriodVanishing [T2Space G] [LocallyCompactSpace G]
    (hle : Γ ≤ H) (hΓ : IsDiscrete (Γ : Set G)) (hH : IsClosed (H : Set G))
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (μH : Measure H) [SFinite μH] [IsFiniteMeasureOnCompacts μH]
    [μH.IsMulLeftInvariant] [μH.IsMulRightInvariant]
    (ν : Measure (LeftCosetSpace H)) :
    ClosedSubgroupPeriodVanishingStatement hle hΓ hH μG μH ν := by
  intro hν f hf hInv hInt hPeriods
  let d := fundamentalDomain Γ hΓ
  have hd : MeasurableSet d := measurableSet_fundamentalDomain Γ hΓ
  let κ := orbitKernel H hH μH
  let f₀ := d.indicator f
  have hf₀ : Measurable f₀ := hf.indicator hd
  have hcomp : κ ∘ₘ ν = μG := orbitKernel_comp H hH μH μG ν hν
  have hfInt : Integrable f₀ (κ ∘ₘ ν) := by
    rw [hcomp]
    exact (integrable_indicator_iff hd).2 hInt
  have hFubini :
      ∫ x, f₀ x ∂(κ ∘ₘ ν) = ∫ q, ∫ x, f₀ x ∂κ q ∂ν := by
    rw [Measure.comp_eq_comp_const_apply] at hfInt ⊢
    simpa only [Kernel.const_apply] using Kernel.integral_comp hfInt
  have hΓH := hΓ.preimage continuous_subtype_val.continuousOn
    (Subtype.val_injective : Function.Injective (Subtype.val : H → G))
  let : Countable (Γ.comap H.subtype) := countable_of_isDiscrete _ hΓH
  have hInner (q : LeftCosetSpace H) : ∫ x, f₀ x ∂κ q = 0 := by
    induction q using Quotient.inductionOn with
    | _ g =>
      change (∫ x, f₀ x ∂κ (mk H g)) = 0
      rw [show κ (mk H g) = _ from orbitKernel_mk H hH μH g,
        integral_map (continuous_subtype_val.mul_const g).measurable.aemeasurable
          hf₀.aestronglyMeasurable]
      change ∫ h : H, d.indicator f (h.val * g) ∂μH = 0
      have hfun : (fun h : H => d.indicator f (h.val * g)) =
          (subgroupSlice H d g).indicator (fun h => f (h.val * g)) := by
        funext h
        by_cases hm : h.val * g ∈ d <;> simp [subgroupSlice, hm]
      rw [hfun, integral_indicator (measurableSet_subgroupSlice H hd g)]
      have hslice := isFundamentalDomain_subgroupSlice Γ H hle hd
        (fundamentalDomain_unique Γ hΓ) g μH
      rw [hslice.setIntegral_eq (isFundamentalDomain (Γ.comap H.subtype) hΓH μH)]
      · exact hPeriods g
      · intro δ h
        change f (((δ.val : H).val * h.val) * g) = f (h.val * g)
        rw [mul_assoc]
        exact hInv ⟨δ.val.val, δ.property⟩ (h.val * g)
  rw [hcomp, integral_indicator hd] at hFubini
  simpa only [hInner, integral_zero] using hFubini

end ClosedSubgroup

namespace Semidirect

variable {N : Type u} {M : Type v} {H : Type w}
  [Group N] [Group M] [Group H]
  (i : N →* H) (j : M →* H) (p : H →* M)
  (hpj : ∀ m, p (j m) = m)
  (hker : ∀ h, p h = 1 → ∃ n, i n = h)
  (hpi : ∀ n, p (i n) = 1)
  [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace H]
  [IsTopologicalGroup N] [IsTopologicalGroup M] [IsTopologicalGroup H]
  [SecondCountableTopology N] [SecondCountableTopology M] [SecondCountableTopology H]
  [LocallyCompactSpace N] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [MeasurableSpace N] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace N] [BorelSpace M] [BorelSpace H]
  (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)
  (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  (ΓM : Subgroup M) (hΓM : IsDiscrete (ΓM : Set M))
  (hjΓ : ∀ m ∈ ΓM, j m ∈ Γ) (hpΓ : ∀ h ∈ Γ, p h ∈ ΓM)

include hpj hker hpi hi hj hp hjΓ hpΓ in
/-- The period of a lattice-invariant function on a split
semidirect quotient vanishes if every normal period vanishes. Fubini
applies whenever the full period is absolutely integrable. -/
theorem integral_fundamentalDomain_eq_zero_of_normalPeriods
    (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N))
    [IsFiniteMeasure (haarQuotientMeasure (Γ.comap i) hΓN)]
    [IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)]
    (f : H → ℂ)
    (hInv : ∀ γ : Γ, ∀ h, f (γ.val * h) = f h)
    (hNormal : ∀ m : M, ∫ n in fundamentalDomain (Γ.comap i) hΓN,
      f (i n * j m) ∂Measure.haar = 0) :
    ∫ h in fundamentalDomain Γ hΓ, f h ∂Measure.haar = 0 := by
  classical
  let Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  let E := fundamentalDomain (Γ.comap i) hΓN ×ˢ fundamentalDomain ΓM hΓM
  let ν := (Measure.haar : Measure N).prod (Measure.haar : Measure M)
  obtain ⟨c, hc⟩ := exists_haar_eq_smul_map_prod hpj hker hpi hi hj hp
    (mulEquivHaarChar_conj_eq_one_of_finiteCovolume
      i j p hpj hker hpi hi hj Γ ΓM hΓM hjΓ hΓN)
  have hD := isFundamentalDomain_product i j p hpj hker hpi hi hj hp
    Γ ΓM hΓM hjΓ hpΓ hΓN
  let : Countable Γ := countable_of_isDiscrete Γ hΓ
  rw [(isFundamentalDomain Γ hΓ Measure.haar).setIntegral_eq hD hInv]
  change (∫ h in Φ '' E, f h ∂Measure.haar) = 0
  by_cases hI : IntegrableOn f (Φ '' E) Measure.haar
  · rw [hc, Measure.restrict_smul, integral_smul_nnreal_measure]
    change c • (∫ h in Φ '' E, f h ∂ν.map Φ) = 0
    by_cases hc₀ : c = 0
    · simp [hc₀]
    rw [hc, IntegrableOn, Measure.restrict_smul] at hI
    change Integrable f ((c : ℝ≥0∞) • (ν.map Φ).restrict (Φ '' E)) at hI
    rw [integrable_smul_measure (by exact_mod_cast hc₀) ENNReal.coe_ne_top] at hI
    have hmp : MeasurePreserving Φ (ν.restrict E) ((ν.map Φ).restrict (Φ '' E)) := by
      simpa [Φ.preimage_image] using
        (show MeasurePreserving Φ ν (ν.map Φ) from ⟨Φ.continuous.measurable, rfl⟩).restrict_preimage
          (show MeasurableSet (Φ '' E) by
            rw [Φ.image_eq_preimage_symm]
            exact Φ.symm.continuous.measurable
              ((measurableSet_fundamentalDomain (Γ.comap i) hΓN).prod
                (measurableSet_fundamentalDomain ΓM hΓM)))
    have hProd := hmp.integrable_comp_of_integrable hI
    rw [Φ.isClosedEmbedding.setIntegral_map, Φ.preimage_image]
    change Integrable (f ∘ Φ)
      (((Measure.haar : Measure N).prod (Measure.haar : Measure M)).restrict
        (fundamentalDomain (Γ.comap i) hΓN ×ˢ fundamentalDomain ΓM hΓM)) at hProd
    change c • (∫ x in fundamentalDomain (Γ.comap i) hΓN ×ˢ fundamentalDomain ΓM hΓM,
      (f ∘ Φ) x ∂(Measure.haar : Measure N).prod (Measure.haar : Measure M)) = 0
    rw [← Measure.prod_restrict] at hProd ⊢
    rw [integral_prod_symm _ hProd]
    simp only [Function.comp_apply, Φ, prodHomeomorph_apply, hNormal, integral_zero, smul_zero]
  · exact integral_undef hI

end Semidirect

end Langlands.Global.LeftCosetSpace

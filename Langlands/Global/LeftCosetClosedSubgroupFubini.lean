import Langlands.Global.LeftCosetClosedQuotientMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Quotient integration through a closed subgroup containing the lattice -/

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal ProbabilityTheory

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

open Langlands.QuotientIntegration

private theorem subgroupSlice_indicator {G : Type u} [Group G] (H : Subgroup G)
    {E : Type*} [Zero E] (f : G → E) (D : Set G) (g : G) :
    (fun h : H => D.indicator f (h.val * g)) = (subgroupSlice H D g).indicator (fun h => f (h.val * g)) := by
  funext h
  by_cases hm : h.val * g ∈ D <;> simp [subgroupSlice, hm]

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {Γ H : Subgroup G} [BorelSpace H] [BorelSpace (LeftCosetSpace H)]

private local instance : SecondCountableTopology H := secondCountableTopology_induced _ G Subtype.val

variable (hΓ : IsDiscrete (Γ : Set G))

local notation "ΓH" => Γ.comap H.subtype
local notation "disp" => (hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective)
local notation "dG" => fundamentalDomain Γ hΓ
local notation "dH" => fundamentalDomain ΓH disp

/-- The fundamental-domain integral for the discrete quotient is the iterated
integral on the closed quotient and the discrete quotient of its subgroup,
for measures as in the compatibility premise. -/
def ClosedSubgroupFubiniStatement
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (μH : Measure H) [SFinite μH] [IsFiniteMeasureOnCompacts μH]
    [μH.IsMulLeftInvariant] [μH.IsMulRightInvariant] (ν : Measure (LeftCosetSpace H)) : Prop :=
  Γ ≤ H → IsClosed (H : Set G) → IsCompatible H μG μH ν →
    (∀ f : G → ℂ, Measurable f → (∀ γ : Γ, ∀ g, f (γ.val * g) = f g) →
      IntegrableOn f dG μG →
      Integrable (fun q : LeftCosetSpace H => ∫ h in dH, f (h.val * q.out) ∂μH) ν ∧
      (∫ g in dG, f g ∂μG) = ∫ q, ∫ h in dH, f (h.val * q.out) ∂μH ∂ν) ∧
    (∀ f : G → ℝ≥0∞, Measurable f → (∀ γ : Γ, ∀ g, f (γ.val * g) = f g) →
      (∫⁻ g in dG, f g ∂μG) = ∫⁻ q, ∫⁻ h in dH, f (h.val * q.out) ∂μH ∂ν)

variable (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
  (μH : Measure H) [SFinite μH] [IsFiniteMeasureOnCompacts μH]
  [μH.IsMulLeftInvariant] [μH.IsMulRightInvariant] (ν : Measure (LeftCosetSpace H))

set_option maxHeartbeats 1000000 in
theorem closedSubgroupFubini : ClosedSubgroupFubiniStatement (Γ := Γ) hΓ μG μH ν := by
  intro hle hH hν
  let D := dG
  let E := dH
  let κ := orbitKernel H hH μH
  have hD : MeasurableSet D := measurableSet_fundamentalDomain Γ hΓ
  have hcomp : κ ∘ₘ ν = μG := orbitKernel_comp H hH μH μG ν hν
  have hKernel (q : LeftCosetSpace H) :
      κ q = Measure.map (fun h : H => h.val * q.out) μH := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hSlice (g : G) : IsFundamentalDomain ΓH (subgroupSlice H D g) μH :=
    isFundamentalDomain_subgroupSlice Γ H hle hD (fundamentalDomain_unique Γ hΓ) g μH
  have hE : IsFundamentalDomain ΓH E μH := isFundamentalDomain ΓH disp μH
  let : Countable ΓH := countable_of_isDiscrete ΓH disp
  have hInvOnH {B : Type} (f : G → B) (hf : ∀ γ : Γ, ∀ g, f (γ.val * g) = f g)
      (x : G) (δ : ΓH) (h : H) : f ((δ • h).val * x) = f (h.val * x) := by
    change f (((δ.val : H).val * h.val) * x) = f (h.val * x)
    rw [mul_assoc]
    exact hf ⟨δ.val.val, δ.property⟩ (h.val * x)
  constructor
  · intro f hf hInv hInt
    let f₀ := D.indicator f
    have hf₀ : Measurable f₀ := hf.indicator hD
    have hOuter (q : LeftCosetSpace H) :
        ∫ x, f₀ x ∂κ q = ∫ h in E, f (h.val * q.out) ∂μH := by
      rw [hKernel, integral_map (continuous_subtype_val.mul_const q.out).measurable.aemeasurable
        hf₀.aestronglyMeasurable]
      change ∫ h : H, D.indicator f (h.val * q.out) ∂μH = _
      rw [subgroupSlice_indicator, integral_indicator (measurableSet_subgroupSlice H hD q.out)]
      exact (hSlice q.out).setIntegral_eq hE (hInvOnH f hInv q.out)
    have hfInt : Integrable f₀ (κ ∘ₘ ν) := by
      rw [hcomp]
      exact (integrable_indicator_iff hD).mpr hInt
    have hFubini : ∫ x, f₀ x ∂(κ ∘ₘ ν) = ∫ q, ∫ x, f₀ x ∂κ q ∂ν := by
      rw [Measure.comp_eq_comp_const_apply] at hfInt ⊢
      simpa only [Kernel.const_apply] using Kernel.integral_comp hfInt
    have hIntOuter : Integrable (fun q => ∫ x, f₀ x ∂κ q) ν := by
      rw [Measure.comp_eq_comp_const_apply] at hfInt
      simpa only [Kernel.const_apply] using hfInt.integral_comp
    refine ⟨?_, ?_⟩
    · simpa only [hOuter] using hIntOuter
    · rw [hcomp, integral_indicator hD] at hFubini
      simpa only [hOuter] using hFubini
  · intro f hf hInv
    let f₀ := D.indicator f
    have hf₀ : Measurable f₀ := hf.indicator hD
    have hOuter (q : LeftCosetSpace H) :
        ∫⁻ x, f₀ x ∂κ q = ∫⁻ h in E, f (h.val * q.out) ∂μH := by
      rw [hKernel, lintegral_map hf₀ (continuous_subtype_val.mul_const q.out).measurable]
      change ∫⁻ h : H, D.indicator f (h.val * q.out) ∂μH = _
      rw [subgroupSlice_indicator, lintegral_indicator (measurableSet_subgroupSlice H hD q.out)]
      exact (hSlice q.out).setLIntegral_eq hE _ (hInvOnH f hInv q.out)
    have hFubini : (∫⁻ q, ∫⁻ x, f₀ x ∂κ q ∂ν) = ∫⁻ x, D.indicator f x ∂μG :=
      lintegral_orbitKernel H hH μH μG ν hν f₀ hf₀
    rw [lintegral_indicator hD] at hFubini
    simpa only [hOuter] using hFubini.symm

end Langlands.Global.LeftCosetSpace

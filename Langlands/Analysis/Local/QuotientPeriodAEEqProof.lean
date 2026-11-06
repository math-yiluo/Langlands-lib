import Langlands.Analysis.Local.QuotientPeriodAEEqStatement

noncomputable section

universe uG uH

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set
open Langlands.Global
open scoped Pointwise

section Lift

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
  (μ : Measure G) [SMulInvariantMeasure Γ G μ]

/-- Null quotient assertions lift through the actual countable fundamental-domain cover. -/
theorem ae_lift_discreteQuotientMeasure {p : LeftCosetSpace Γ → Prop}
    (hp : ∀ᵐ q ∂LeftCosetSpace.discreteQuotientMeasure Γ hΓ μ, p q) :
    ∀ᵐ g ∂μ, p (LeftCosetSpace.mk Γ g) := by
  let := LeftCosetSpace.countable_of_isDiscrete Γ hΓ
  have hs := LeftCosetSpace.isFundamentalDomain Γ hΓ μ
  rw [← hs.sum_restrict]
  apply ae_sum_iff.mpr
  intro γ
  have hγ := hs.smul γ
  have heq := LeftCosetSpace.discreteQuotientMeasure_eq Γ hΓ μ hγ
  rw [heq] at hp
  exact (LeftCosetSpace.measurePreserving_mk Γ μ _).quasiMeasurePreserving.ae hp

end Lift

/-- The exact representative-congruence target, including separate absolute convergence. -/
theorem quotientPeriodAEEq : QuotientPeriodAEEqStatement.{uG, uH} := by
  intro G _ _ _ _ _ _ _ _ Γ hΓ _ μ _ H _ _ _ _ _ _ _ _ Λ hΛ _ μH _
    j hj hjΛ χ hχ hχΛ φ ψ hφ hψ heq
  let s := LeftCosetSpace.fundamentalDomain Λ hΛ
  have hlift := ae_lift_discreteQuotientMeasure Γ hΓ μ heq
  have hfiber : ∀ᵐ h ∂μH.restrict s, ∀ᵐ g ∂μ,
      φ (LeftCosetSpace.mk Γ (j h * g)) = ψ (LeftCosetSpace.mk Γ (j h * g)) := by
    filter_upwards with h
    exact (measurePreserving_mul_left μ (j h)).quasiMeasurePreserving.ae hlift
  have hjoint : MeasurableSet {p : H × G |
      φ (LeftCosetSpace.mk Γ (j p.1 * p.2)) = ψ (LeftCosetSpace.mk Γ (j p.1 * p.2))} :=
    measurableSet_eq_fun
      (hφ.measurable.comp ((LeftCosetSpace.continuous_mk Γ).comp
        ((hj.comp continuous_fst).mul continuous_snd)).measurable)
      (hψ.measurable.comp ((LeftCosetSpace.continuous_mk Γ).comp
        ((hj.comp continuous_fst).mul continuous_snd)).measurable)
  have hswap := (ae_ae_comm hjoint).mp hfiber
  filter_upwards [hswap] with g hg
  have hq : ∀ᵐ q ∂LeftCosetSpace.quotientMeasure Λ μH s,
      φ (periodOrbitMap Γ Λ j hjΛ g q) = ψ (periodOrbitMap Γ Λ j hjΛ g q) := by
    change ∀ᵐ q ∂Measure.map (LeftCosetSpace.mk Λ) (μH.restrict s), _
    apply (ae_map_iff (LeftCosetSpace.measurable_mk Λ).aemeasurable
      (measurableSet_eq_fun
        (hφ.measurable.comp (continuous_periodOrbitMap Γ Λ j hjΛ hj g).measurable)
        (hψ.measurable.comp (continuous_periodOrbitMap Γ Λ j hjΛ hj g).measurable))).mpr
    exact hg
  have hqn := ae_smul_measure hq ((μH s)⁻¹)
  have hint : periodIntegrand Γ Λ j hjΛ χ hχΛ φ g =ᵐ[
      LeftCosetSpace.normalizedMeasure Λ μH s]
        periodIntegrand Γ Λ j hjΛ χ hχΛ ψ g := by
    filter_upwards [hqn] with q hq'
    exact congrArg (fun z : ℂ => (periodQuotientCharacter Λ χ hχΛ q : ℂ)⁻¹ * z) hq'
  exact ⟨hint, integrable_congr hint, integral_congr_ae hint⟩

end Langlands.QuotientIntegration

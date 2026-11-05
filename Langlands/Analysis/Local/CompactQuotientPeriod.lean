import Langlands.Global.LeftCosetFundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section

universe uG uH

namespace Langlands.QuotientIntegration

open MeasureTheory Set
open Langlands.Global

variable {G : Type uG} [Group G] {H : Type uH} [Group H]
  (Γ : Subgroup G) (Λ : Subgroup H) (j : H →* G)
  (hjΛ : ∀ η : Λ, j η ∈ Γ)

/-- The actual left-period orbit, including its right-translation parameter. -/
def periodOrbitMap (g : G) :
    LeftCosetSpace Λ → LeftCosetSpace Γ :=
  LeftCosetSpace.lift Λ (fun h => LeftCosetSpace.mk Γ (j h * g)) (by
    intro η h
    rw [map_mul, mul_assoc]
    exact LeftCosetSpace.mk_subgroup_mul Γ ⟨j η, hjΛ η⟩ (j h * g))

@[simp]
theorem periodOrbitMap_mk (g : G) (h : H) :
    periodOrbitMap Γ Λ j hjΛ g (LeftCosetSpace.mk Λ h) =
      LeftCosetSpace.mk Γ (j h * g) := rfl

variable (χ : H →* ℂˣ) (hχΛ : ∀ η : Λ, χ η = 1)

/-- A possibly nonunitary character descends when it is trivial on the subgroup. -/
def periodQuotientCharacter : LeftCosetSpace Λ → ℂˣ :=
  LeftCosetSpace.lift Λ χ (by
    intro η h
    rw [map_mul, hχΛ η, one_mul])

@[simp]
theorem periodQuotientCharacter_mk (h : H) :
    periodQuotientCharacter Λ χ hχΛ (LeftCosetSpace.mk Λ h) = χ h := rfl

/-- The actual quotient-period integrand; convergence is a separate property. -/
def periodIntegrand (φ : LeftCosetSpace Γ → ℂ) (g : G) :
    LeftCosetSpace Λ → ℂ :=
  fun q => (periodQuotientCharacter Λ χ hχΛ q : ℂ)⁻¹ *
    φ (periodOrbitMap Γ Λ j hjΛ g q)

@[simp]
theorem periodIntegrand_mk (φ : LeftCosetSpace Γ → ℂ) (g : G) (h : H) :
    periodIntegrand Γ Λ j hjΛ χ hχΛ φ g (LeftCosetSpace.mk Λ h) =
      (χ h : ℂ)⁻¹ * φ (LeftCosetSpace.mk Γ (j h * g)) := rfl

section Measure

variable [MeasurableSpace H] (νQ : Measure (LeftCosetSpace Λ))

/-- Absolute convergence of the specified actual quotient period. -/
def HasConvergentQuotientCharacterPeriod (φ : LeftCosetSpace Γ → ℂ) (g : G) : Prop :=
  Integrable (periodIntegrand Γ Λ j hjΛ χ hχΛ φ g) νQ

/-- The total Bochner period on the actual quotient and supplied measure. -/
def quotientCharacterPeriod (φ : LeftCosetSpace Γ → ℂ) (g : G) : ℂ :=
  ∫ q, periodIntegrand Γ Λ j hjΛ χ hχΛ φ g q ∂νQ

end Measure

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H]

theorem continuous_periodOrbitMap (hj : Continuous j) (g : G) :
    Continuous (periodOrbitMap Γ Λ j hjΛ g) :=
  LeftCosetSpace.continuous_lift Λ _ _ ((LeftCosetSpace.continuous_mk Γ).comp
    (hj.mul_const g))

theorem continuous_periodQuotientCharacter (hχ : Continuous χ) :
    Continuous (periodQuotientCharacter Λ χ hχΛ) :=
  LeftCosetSpace.continuous_lift Λ _ _ hχ

theorem continuous_periodIntegrand (hj : Continuous j) (hχ : Continuous χ)
    {φ : LeftCosetSpace Γ → ℂ} (hφ : Continuous φ) (g : G) :
    Continuous (periodIntegrand Γ Λ j hjΛ χ hχΛ φ g) :=
  ((Units.continuous_val.comp (continuous_periodQuotientCharacter Λ χ hχΛ hχ)).inv₀
    (fun _ => Units.ne_zero _)).mul
      (hφ.comp (continuous_periodOrbitMap Γ Λ j hjΛ hj g))

section Borel

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (LeftCosetSpace Γ)] [BorelSpace (LeftCosetSpace Γ)]
  [BorelSpace (LeftCosetSpace Λ)]

omit [MeasurableSpace G] [BorelSpace G] [BorelSpace H] in
theorem stronglyMeasurable_periodIntegrand (hj : Continuous j) (hχ : Continuous χ)
    {φ : LeftCosetSpace Γ → ℂ} (hφ : StronglyMeasurable φ) (g : G) :
    StronglyMeasurable (periodIntegrand Γ Λ j hjΛ χ hχΛ φ g) :=
  (((Units.continuous_val.comp (continuous_periodQuotientCharacter Λ χ hχΛ hχ)).inv₀
    (fun _ => Units.ne_zero _)).stronglyMeasurable).mul
      (hφ.comp_measurable (continuous_periodOrbitMap Γ Λ j hjΛ hj g).measurable)

omit [MeasurableSpace G] [BorelSpace G] [BorelSpace H]
  [MeasurableSpace (LeftCosetSpace Γ)] [BorelSpace (LeftCosetSpace Γ)] in
theorem hasConvergentQuotientCharacterPeriod_of_continuous
    [CompactSpace (LeftCosetSpace Λ)]
    (νQ : Measure (LeftCosetSpace Λ)) [IsFiniteMeasure νQ]
    (hj : Continuous j) (hχ : Continuous χ)
    {φ : LeftCosetSpace Γ → ℂ} (hφ : Continuous φ) (g : G) :
    HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ νQ φ g := by
  exact (continuous_periodIntegrand Γ Λ j hjΛ χ hχΛ hj hχ hφ g).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

end Borel
end Topology

section NormalizedDomain

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (LeftCosetSpace Γ)] [BorelSpace (LeftCosetSpace Γ)]
  [BorelSpace (LeftCosetSpace Λ)]
  (hΛ : IsDiscrete (Λ : Set H)) (νH : Measure H)

/-- The actual normalized quotient period using the existing canonical Borel domain. -/
def normalizedQuotientCharacterPeriod (φ : LeftCosetSpace Γ → ℂ) (g : G) : ℂ :=
  quotientCharacterPeriod Γ Λ j hjΛ χ hχΛ
    (LeftCosetSpace.normalizedMeasure Λ νH (LeftCosetSpace.fundamentalDomain Λ hΛ)) φ g

omit [MeasurableSpace G] [BorelSpace G] in
theorem normalizedQuotientCharacterPeriod_eq_domain
    [SMulInvariantMeasure Λ H νH]
    (hj : Continuous j) (hχ : Continuous χ)
    {φ : LeftCosetSpace Γ → ℂ} (hφ : StronglyMeasurable φ)
    (s : Set H) (hs : IsFundamentalDomain Λ s νH) (g : G) :
    normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ νH φ g =
      ((νH s)⁻¹).toReal •
        ∫ h in s, (χ h : ℂ)⁻¹ * φ (LeftCosetSpace.mk Γ (j h * g)) ∂νH := by
  let := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  have heq := LeftCosetSpace.normalizedMeasure_eq Λ νH
    (LeftCosetSpace.isFundamentalDomain Λ hΛ νH) hs
  unfold normalizedQuotientCharacterPeriod quotientCharacterPeriod
  rw [heq, LeftCosetSpace.normalizedMeasure, integral_smul_measure]
  congr 1
  exact LeftCosetSpace.integral_quotientMeasure Λ νH s _
    (stronglyMeasurable_periodIntegrand Γ Λ j hjΛ χ hχΛ hj hχ hφ g).aestronglyMeasurable

end NormalizedDomain

end Langlands.QuotientIntegration

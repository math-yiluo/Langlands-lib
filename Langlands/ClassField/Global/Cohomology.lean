import Langlands.ClassField.Global.Cocycle
import Langlands.GroupTheory.CocycleCohomology

/-! # Actual relative idele-class cohomology and normalized representatives -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u v

variable (K : Type u) (E : Type v) [Field K] [Field E]
  [NumberField E] [Algebra K E]

attribute [local instance] relativeIdeleClassAction

/-- The additive wrapper of the genuine idele-class group, with its arithmetic action. -/
abbrev relativeIdeleClassRepresentation :
    Rep.{v} NormalizedTwoCocycle.CoefficientScalars.{v} (E ≃ₐ[K] E) :=
  NormalizedTwoCocycle.coefficientRepresentation (E ≃ₐ[K] E) (IdeleClassGroup (𝓞 E) E)

@[simp] theorem relativeIdeleClassRepresentation_apply (σ : E ≃ₐ[K] E)
    (a : Additive (IdeleClassGroup (𝓞 E) E)) :
    (relativeIdeleClassRepresentation K E).ρ σ a =
      Additive.ofMul (relativeIdeleClassAut K E σ a.toMul) := rfl

/-- On idele representatives this is the published arithmetic action on the actual quotient. -/
theorem relativeIdeleClassRepresentation_apply_mk (σ : E ≃ₐ[K] E)
    (a : IdeleGroup (𝓞 E) E) :
    (relativeIdeleClassRepresentation K E).ρ σ
        (Additive.ofMul (QuotientGroup.mk a : IdeleClassGroup (𝓞 E) E)) =
      Additive.ofMul (QuotientGroup.mk (ideleEquiv σ.toRingEquiv a) :
        IdeleClassGroup (𝓞 E) E) := rfl

/-- Ordinary relative group cohomology in every degree, computed by Mathlib's complex. -/
abbrev relativeIdeleClassCohomology (n : ℕ) :
    ModuleCat.{v} NormalizedTwoCocycle.CoefficientScalars.{v} :=
  groupCohomology (relativeIdeleClassRepresentation K E) n

/-- The one-cochain differential, with the precise arithmetic action and sign convention. -/
theorem relativeIdeleClass_differential₁₂
    (b : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E) (σ τ : E ≃ₐ[K] E) :
    groupCohomology.d₁₂ (relativeIdeleClassRepresentation K E)
        (Additive.ofMul ∘ b) (σ, τ) =
      Additive.ofMul ((relativeIdeleClassAut K E σ (b τ)) / b (σ * τ) * b σ) := rfl

/-- The two-cochain differential has the matching multiplicative convention. -/
theorem relativeIdeleClass_differential₂₃
    (f : (E ≃ₐ[K] E) × (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E)
    (σ τ υ : E ≃ₐ[K] E) :
    groupCohomology.d₂₃ (relativeIdeleClassRepresentation K E)
        (Additive.ofMul ∘ f) (σ, τ, υ) =
      Additive.ofMul ((relativeIdeleClassAut K E σ (f (τ, υ))) / f (σ * τ, υ) *
        f (σ, τ * υ) / f (σ, τ)) := rfl

namespace RelativeIdeleCocycle

variable {K E}

/-- The actual additive two-cocycle associated to a normalized relative idele cocycle. -/
abbrev toCocycle₂ (c : RelativeIdeleCocycle K E) :
    groupCohomology.cocycles₂ (relativeIdeleClassRepresentation K E) :=
  NormalizedTwoCocycle.toCocycle₂ c

/-- The class of the given cocycle in the actual second relative idele-class cohomology. -/
abbrev cohomologyClass (c : RelativeIdeleCocycle K E) :
    relativeIdeleClassCohomology K E 2 :=
  NormalizedTwoCocycle.cohomologyClass c

@[simp] theorem toCocycle₂_apply (c : RelativeIdeleCocycle K E) (σ τ : E ≃ₐ[K] E) :
    toCocycle₂ c (σ, τ) = Additive.ofMul (c (σ, τ)) := rfl

/-- Normalize an actual additive cocycle without changing its class. -/
abbrev normalizedRepresentative
    (f : groupCohomology.cocycles₂ (relativeIdeleClassRepresentation K E)) :
    RelativeIdeleCocycle K E :=
  NormalizedTwoCocycle.normalizedRepresentative f

theorem normalizedRepresentative_apply
    (f : groupCohomology.cocycles₂ (relativeIdeleClassRepresentation K E))
    (σ τ : E ≃ₐ[K] E) :
    normalizedRepresentative f (σ, τ) =
      @Additive.toMul (IdeleClassGroup (𝓞 E) E) (f (σ, τ)) /
        relativeIdeleClassAut K E σ (@Additive.toMul (IdeleClassGroup (𝓞 E) E) (f (1, 1))) :=
  NormalizedTwoCocycle.normalizedRepresentative_apply f σ τ

theorem cohomologyClass_normalizedRepresentative
    (f : groupCohomology.cocycles₂ (relativeIdeleClassRepresentation K E)) :
    cohomologyClass (normalizedRepresentative f) =
      groupCohomology.H2π (relativeIdeleClassRepresentation K E) f :=
  NormalizedTwoCocycle.cohomologyClass_normalizedRepresentative f

/-- Every actual degree-two class has a normalized multiplicative idele-class representative. -/
theorem cohomologyClass_surjective :
    Function.Surjective (cohomologyClass (K := K) (E := E)) :=
  NormalizedTwoCocycle.cohomologyClass_surjective

/-- An explicit cochain relating two relative cocycles identifies their actual classes. -/
theorem cohomologyClass_eq_of_cochain (c d : RelativeIdeleCocycle K E)
    (b : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E)
    (hb : ∀ σ τ, c (σ, τ) * b (σ * τ) = b σ * (σ • b τ) * d (σ, τ)) :
    cohomologyClass c = cohomologyClass d :=
  NormalizedTwoCocycle.cohomologyClass_eq_of_cochain c d b hb

/-- Identity-component extension map data induce equal cohomology classes. -/
theorem cohomologyClass_eq_of_mapData {c d : RelativeIdeleCocycle K E}
    (m : NormalizedTwoCocycle.MapData c d (MonoidHom.id _) (MonoidHom.id _)) :
    cohomologyClass c = cohomologyClass d :=
  NormalizedTwoCocycle.MapData.cohomologyClass_eq m

end RelativeIdeleCocycle
end Langlands.ClassField.Global

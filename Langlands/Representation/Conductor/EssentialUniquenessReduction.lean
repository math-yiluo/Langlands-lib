import Langlands.Representation.Conductor.EssentialRestrictionUniqueness

/-!
# Uniqueness of the essential vector from mirabolic restriction injectivity

If the map `v ↦ (p ↦ ℓ(π(p) v))` from the representation space to functions on the
mirabolic subgroup is injective, then a model vector vanishing on the mirabolic
subgroup is zero. Two essential vectors agree on the mirabolic subgroup, so under
this injectivity there is at most one essential vector, and existence of one gives
the unique existence required by Jacquet 2012, Theorem 1.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg

universe uF uV

section Restriction

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
variable {ψ : UnitaryAdditiveCharacter F} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)

/-- Injectivity of restriction to the mirabolic subgroup of `GL_(n+2)`:
`v ↦ (p ↦ ℓ(π(p) v))` is injective on the representation space. -/
def IsMirabolicRestrictionInjective : Prop :=
  Function.Injective (fun v : V => fun p : mirabolic (n + 1) F => ℓ.val (π p.val v))

/-- Under mirabolic restriction injectivity, a vector of the model of `ℓ` that
vanishes on the mirabolic subgroup is zero. -/
theorem eq_zero_of_mirabolic_eq_zero (hinj : IsMirabolicRestrictionInjective π ℓ)
    (w : (coefficientModel π ℓ).toSubmodule)
    (hw : ∀ p : mirabolic (n + 1) F, w.val.val p.val = 0) : w = 0 := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ w
  have hv : (fun p : mirabolic (n + 1) F => ℓ.val (π p.val v)) =
      fun p : mirabolic (n + 1) F => ℓ.val (π p.val 0) := by
    funext p
    rw [map_zero, map_zero]
    exact hw p
  rw [hinj hv, map_zero]

end Restriction

section Essential

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)

/-- Under mirabolic restriction injectivity, two essential vectors of a smooth
representation coincide. -/
theorem IsEssentialVector.eq_of_mirabolicRestrictionInjective (hπ : IsSmooth π)
    (hinj : IsMirabolicRestrictionInjective π ℓ)
    {w₁ w₂ : (coefficientModel π ℓ).toSubmodule}
    (h₁ : IsEssentialVector h π ℓ w₁) (h₂ : IsEssentialVector h π ℓ w₂) : w₁ = w₂ := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mirabolic_eq_zero π ℓ hinj
  intro p
  change w₁.val.val p.val - w₂.val.val p.val = 0
  rw [IsEssentialVector.eq_on_mirabolic h π ℓ hπ h₁ h₂ p, sub_self]

/-- Under mirabolic restriction injectivity, the existence of an essential vector
gives its unique existence. -/
theorem existsUnique_isEssentialVector_of_exists (hπ : IsSmooth π)
    (hinj : IsMirabolicRestrictionInjective π ℓ)
    (hex : ∃ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w) :
    ∃! w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w := by
  obtain ⟨w, hw⟩ := hex
  exact ⟨w, hw, fun w' hw' =>
    IsEssentialVector.eq_of_mirabolicRestrictionInjective h π ℓ hπ hinj hw' hw⟩

/-- The same for a generic representation, whose admissibility includes
smoothness. -/
theorem existsUnique_isEssentialVector_of_isGeneric (hgen : IsGeneric ψ (n + 1) π)
    (hinj : IsMirabolicRestrictionInjective π ℓ)
    (hex : ∃ w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w) :
    ∃! w : (coefficientModel π ℓ).toSubmodule, IsEssentialVector h π ℓ w :=
  existsUnique_isEssentialVector_of_exists h π ℓ hgen.2.1.1 hinj hex

end Essential

end Langlands.Conductor

import Langlands.Weil.Representation.CharacterLine
import Langlands.VirtualRepresentation.ExactDual

/-!
# Contragredients of actual character lines

Evaluation on the unit vector identifies the full algebraic dual of the
lifted scalar line with the line of the inverse character.
-/

noncomputable section

universe uG uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- Evaluation on the lifted unit vector, with inverse-character action. -/
def dualCharacterLineEquiv (χ : G →* ℂˣ) :
    Equiv (dual (characterLine.{uG, uV} χ))
      (characterLine.{uG, uV} χ⁻¹) where
  toLinearEquiv :=
    (ULift.moduleEquiv.symm.dualMap.trans
      (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ)).trans ULift.moduleEquiv.symm
  isIntertwining' g := by
    ext f
    apply ULift.ext
    let ℓ : Module.Dual ℂ (ULift.{uV} ℂ) := f
    change ℓ ((χ g⁻¹ : ℂ) • (ULift.up (1 : ℂ))) =
      (χ⁻¹ g : ℂ) * ℓ (ULift.up (1 : ℂ))
    rw [map_smul]
    simp

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Full contragredient duality sends the genuine character class to its
inverse-character class in every carrier universe. -/
@[simp]
theorem continuousDual_characterClass (χ : G →ₜ* ℂˣ) :
    continuousDual (characterClass.{uG, uV} χ) =
      characterClass.{uG, uV} χ⁻¹ := by
  unfold characterClass
  rw [continuousDual_ofRepresentation]
  exact ofRepresentation_eq_of_equiv _
    (FiniteRepresentation.dualCharacterLineEquiv χ.toMonoidHom)

/-- Norm-character twisting of a dual line is the line of the product with
the inverse character. -/
theorem continuousTwist_continuousDual_characterClass (ν χ : G →ₜ* ℂˣ) :
    continuousTwist ν (continuousDual (characterClass.{uG, uV} χ)) =
      characterClass.{uG, uV} (ν * χ⁻¹) := by
  rw [continuousDual_characterClass, continuousTwist_characterClass]

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

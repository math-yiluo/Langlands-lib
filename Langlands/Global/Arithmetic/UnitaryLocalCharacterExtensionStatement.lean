import Langlands.Global.HeckeCharacter

/-!
# Unitary extension of a finite local character

This proposition uses the actual completion and idele-class quotient.
Its proof is a separate obligation.
-/

universe u

namespace Langlands.Global

/-- Every continuous modulus-one character of one finite completion extends
to a globally unitary Hecke character with exactly that finite component. -/
def UnitaryLocalCharacterExtensionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (v : FinitePlace F)
    (χ : (FiniteCompletion F v)ˣ →ₜ* ℂˣ),
    (∀ a : (FiniteCompletion F v)ˣ, ‖(χ a : ℂ)‖ = 1) →
    ∃ χ' : HeckeCharacter F, χ'.IsUnitary ∧ χ'.finiteComponent v = χ

end Langlands.Global

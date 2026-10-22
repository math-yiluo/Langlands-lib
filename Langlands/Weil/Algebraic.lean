import Langlands.Weil.Pullback

/-! # Algebraic interface: a proposition definition, not a proved theorem. -/

namespace Langlands.Weil

universe u

/-- The integer map is injective; the pullback projects onto the integer
Frobenius preimage; its degree kernel is the embedded original inertia; and
surjectivity of the input homomorphism implies surjectivity of degree. -/
def AlgebraicProperties : Prop :=
  Function.Injective frobenius ∧
  ∀ (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (φ : Γ →ₜ* ProfiniteIntegers),
    φ.comp (projection φ) = frobenius.comp (degree φ) ∧
    Function.Injective (projection φ) ∧
    (projection φ).toMonoidHom.range =
      frobenius.toMonoidHom.range.comap φ.toMonoidHom ∧
    Function.Injective (inertiaInclusion φ) ∧
    (projection φ).toMonoidHom.comp (inertiaInclusion φ).toMonoidHom =
      (inertia φ).subtype ∧
    (inertiaInclusion φ).toMonoidHom.range = inertiaSubgroup φ ∧
    (Function.Surjective φ → Function.Surjective (degree φ))

end Langlands.Weil

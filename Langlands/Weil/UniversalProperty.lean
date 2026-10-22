import Langlands.Weil.Pullback

/-! # Pullback universal properties, stated for later proof. -/

namespace Langlands.Weil

universe u v

/-- Both algebraic and continuous compatible pairs of homomorphisms factor
uniquely through the generic Weil pullback. -/
def UniversalProperty : Prop :=
  ∀ (Γ : Type u) [Group Γ] [TopologicalSpace Γ]
    (φ : Γ →ₜ* ProfiniteIntegers),
    (∀ (H : Type v) [Group H] (a : H →* Γ) (b : H →* Degree),
      φ.toMonoidHom.comp a = frobenius.toMonoidHom.comp b →
      ∃! h : H →* Pullback φ,
        (projection φ).toMonoidHom.comp h = a ∧
        (degree φ).toMonoidHom.comp h = b) ∧
    (∀ (H : Type v) [Group H] [TopologicalSpace H]
      (a : H →ₜ* Γ) (b : H →ₜ* Degree),
      φ.comp a = frobenius.comp b →
      ∃! h : H →ₜ* Pullback φ,
        (projection φ).comp h = a ∧ (degree φ).comp h = b)

end Langlands.Weil

import Langlands.ClassFieldTheory.Local.CyclicNorm
import Langlands.ClassFieldTheory.Local.CyclicClass

/-! # Positive carry classes under the cyclic norm comparison -/

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- The cyclic norm comparison sends the positive carry class for its generator
to the class of the defining base-field unit in the actual norm quotient. -/
def CyclicClassNormNormalization : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) [NeZero n]
    (χ : Gal(L/K) ≃* Multiplicative (ZMod n))
    (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ),
    χ σ = Multiplicative.ofAdd (1 : ZMod n) →
      ∀ a : Kˣ,
        cyclicH2NormEquiv K L σ hσ (cyclicClass K L χ.toMonoidHom a) =
          Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L a)

end Langlands.ClassFieldTheory.Local

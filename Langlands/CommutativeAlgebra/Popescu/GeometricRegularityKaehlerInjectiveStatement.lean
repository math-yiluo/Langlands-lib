import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Geometric regularity and differentials over the prime field -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open scoped TensorProduct

/-- Stacks More on Algebra, Proposition 15.36.1 (07E5), implication (1) ⇒ (4), at a prime of a
geometrically regular algebra. Let `k` be a field of characteristic `p > 0`, `Λ` a Noetherian
geometrically regular `k`-algebra and `q` a prime of `Λ`, with `A = Λ_q` and `K = κ(q)`. Then the
canonical `K`-linear map `K ⊗_k Ω_{k/ℤ} → K ⊗_A Ω_{A/ℤ}`, `c ⊗ ω ↦ c ⊗ ω|_A`, is injective.
(In characteristic `p`, `Ω_{B/ℤ} = Ω_{B/𝔽_p}` for every `k`-algebra `B`.) -/
def GeometricRegularityKaehlerInjectiveStatement : Prop :=
  ∀ (k Λ : Type u) [Field k] [CommRing Λ] [Algebra k Λ] (p : ℕ) [Fact p.Prime] [CharP k p],
    GeometricallyRegular k Λ → ∀ (q : Ideal Λ) [q.IsPrime],
      Function.Injective (LinearMap.liftBaseChange q.ResidueField
        ((TensorProduct.mk (Localization.AtPrime q) q.ResidueField
            Ω[Localization.AtPrime q⁄ℤ] 1).restrictScalars k ∘ₗ
          (KaehlerDifferential.map ℤ ℤ k (Localization.AtPrime q)).restrictScalars k))

end Langlands.CommutativeAlgebra.Popescu

import Langlands.CommutativeAlgebra.Popescu.Basic
import Langlands.CommutativeAlgebra.RegularRingMaps

/-! # Resolution of the local problem in positive characteristic -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.11.4 (07FJ): let `k` be a field of characteristic `p > 0`,
`A` a finitely presented `k`-algebra, `f : A → Λ` a `k`-algebra map to a
Noetherian ring `Λ` that is geometrically regular over `k`, and `q` a prime of
`Λ` minimal over `h_A`. Then `k → A → Λ ⊃ q` can be resolved. -/
def CharPResolutionStatement : Prop :=
  ∀ (k A Λ : Type u) [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [Algebra.FinitePresentation k A] (p : ℕ) [Fact p.Prime] [CharP k p],
    GeometricallyRegular k Λ →
      ∀ (f : A →ₐ[k] Λ) (q : Ideal Λ) [q.IsPrime],
        q ∈ (singularRadical k f).minimalPrimes → CanBeResolved k f q

end Langlands.CommutativeAlgebra.Popescu

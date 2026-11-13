import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Resolution of the local problem in characteristic zero -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.10.3 (07FE), in characteristic zero: let `k` be a field of
characteristic zero, `A` a finitely presented `k`-algebra, `f : A → Λ` a
`k`-algebra map to a Noetherian ring and `q` a prime of `Λ` minimal over `h_A`
such that `Λ_q` is a regular local ring. Then `k → A → Λ ⊃ q` can be resolved.
(In characteristic zero the separability hypothesis (5) of 07FE holds
automatically.) -/
def CharZeroResolutionStatement : Prop :=
  ∀ (k A Λ : Type u) [Field k] [CharZero k] [CommRing A] [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra k A] [Algebra k Λ] [Algebra.FinitePresentation k A] (f : A →ₐ[k] Λ)
    (q : Ideal Λ) [q.IsPrime],
    q ∈ (singularRadical k f).minimalPrimes →
      IsRegularLocalRing (Localization.AtPrime q) → CanBeResolved k f q

end Langlands.CommutativeAlgebra.Popescu

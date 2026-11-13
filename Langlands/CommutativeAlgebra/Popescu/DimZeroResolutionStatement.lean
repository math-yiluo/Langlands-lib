import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Resolving the local problem at a minimal prime -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemmas 16.9.3 (07F9) and 16.9.4 (07FA), in the form used in the proof of
Lemma 16.10.3 (07FE): let `R` and `Λ` be Noetherian, `A` a finitely presented
`R`-algebra, `f : A → Λ` an `R`-algebra map and `q` a minimal prime of `Λ` (so that
`dim Λ_q = 0`) containing `h_A`. If every `R`-algebra map from a finitely presented
`R`-algebra to `Λ_q` factors through a smooth `R`-algebra, then `R → A → Λ ⊃ q` can be
resolved. -/
def DimZeroResolutionStatement : Prop :=
  ∀ (R A Λ : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing Λ]
    [IsNoetherianRing Λ] [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
    (f : A →ₐ[R] Λ) (q : Ideal Λ) [q.IsPrime],
    singularRadical R f ≤ q → q ∈ minimalPrimes Λ →
      HasSmoothFactorizations R (Localization.AtPrime q) → CanBeResolved R f q

end Langlands.CommutativeAlgebra.Popescu

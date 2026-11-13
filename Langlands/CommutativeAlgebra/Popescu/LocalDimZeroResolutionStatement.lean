import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Resolving at a minimal prime from a local smooth factorization -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemmas 16.9.3 (07F9) and 16.9.4 (07FA): let `R` and `Λ` be Noetherian, `A` a finitely
presented `R`-algebra, `f : A → Λ` an `R`-algebra map and `q` a minimal prime of `Λ` (so
`dim Λ_q = 0`) containing `h_A`. Put `p = R ∩ q`. If `A → Λ_q` factors through a smooth
`R_p`-algebra `T`, by ring maps `u : A → T` compatible with `R → R_p → T` and `v : T → Λ_q`
(so that `R_p → A_p → Λ_q ⊃ qΛ_q` can be resolved), then `R → A → Λ ⊃ q` can be resolved. -/
def LocalDimZeroResolutionStatement : Prop :=
  ∀ (R A Λ : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing Λ]
    [IsNoetherianRing Λ] [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
    (f : A →ₐ[R] Λ) (q : Ideal Λ) [q.IsPrime],
    singularRadical R f ≤ q → q ∈ minimalPrimes Λ →
    ∀ (T : Type u) [CommRing T] [Algebra (Localization.AtPrime (q.comap (algebraMap R Λ))) T]
      [Algebra.Smooth (Localization.AtPrime (q.comap (algebraMap R Λ))) T]
      (u : A →+* T) (v : T →+* Localization.AtPrime q),
      u.comp (algebraMap R A) =
        (algebraMap (Localization.AtPrime (q.comap (algebraMap R Λ))) T).comp
          (algebraMap R (Localization.AtPrime (q.comap (algebraMap R Λ)))) →
      v.comp u = (algebraMap Λ (Localization.AtPrime q)).comp f.toRingHom →
      CanBeResolved R f q

end Langlands.CommutativeAlgebra.Popescu

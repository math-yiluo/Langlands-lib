import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Lifting a resolution along a sequence of elements down to dimension zero -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.9.2 (07F8) combined with Lemma 16.9.4 (07FA), in the form used in steps
(18) and (20) of the proof of Lemma 16.11.4 (07FJ). Let `R` and `Λ` be Noetherian, `A` a finitely
presented `R`-algebra, `f : A → Λ` an `R`-algebra map, `q` a prime of `Λ` and `π₁, …, π_r ∈ R`
mapping into `q`, such that `Ann_{R/(π_j⁸ : j < i)}(πᵢ) = Ann_{R/(π_j⁸ : j < i)}(πᵢ²)` and likewise
in `Λ`, and each `πᵢ` maps to a strictly standard element of `A` over `R`. Write
`K = (π₁⁸, …, π_r⁸) ⊆ R`. Assume that for every pair of surjections `σ : R → R₁`, `τ : Λ → Λ₁`
with kernels `K` and `KΛ`, compatible with algebra maps `R → Λ` and `R₁ → Λ₁`, and every prime
`Q` of `Λ₁` over `q`, the prime `Q` is a minimal prime of `Λ₁` and the map `A → Λ → Λ₁ → (Λ₁)_Q`
factors through a smooth algebra `T` over `(R₁)_{Q ∩ R₁}`, compatibly with `R → R₁`. Then
`R → A → Λ ⊃ q` can be resolved. -/
def SequenceDimZeroResolutionStatement : Prop :=
  ∀ (R A Λ : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing Λ]
    [IsNoetherianRing Λ] [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
    (f : A →ₐ[R] Λ) (q : Ideal Λ) [q.IsPrime] (r : ℕ) (π : Fin r → R),
    (∀ i, algebraMap R Λ (π i) ∈ q) →
    (∀ i (x : R), π i ^ 2 * x ∈ Ideal.span ((fun j => π j ^ 8) '' {j | j < i}) →
      π i * x ∈ Ideal.span ((fun j => π j ^ 8) '' {j | j < i})) →
    (∀ i (y : Λ), algebraMap R Λ (π i) ^ 2 * y ∈
        Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i}) →
      algebraMap R Λ (π i) * y ∈
        Ideal.span ((fun j => algebraMap R Λ (π j) ^ 8) '' {j | j < i})) →
    (∀ i, IsStrictlyStandard R (algebraMap R A (π i))) →
    (∀ (R₁ Λ₁ : Type u) [CommRing R₁] [CommRing Λ₁] [Algebra R₁ Λ₁] (σ : R →+* R₁)
      (τ : Λ →+* Λ₁), Function.Surjective σ → Function.Surjective τ →
      RingHom.ker σ = Ideal.span (Set.range fun i => π i ^ 8) →
      RingHom.ker τ = (Ideal.span (Set.range fun i => π i ^ 8)).map (algebraMap R Λ) →
      (∀ x, τ (algebraMap R Λ x) = algebraMap R₁ Λ₁ (σ x)) →
      ∀ (Q : Ideal Λ₁) [Q.IsPrime], Q.comap τ = q →
        Q ∈ minimalPrimes Λ₁ ∧
        ∃ (T : Type u) (_ : CommRing T)
          (_ : Algebra (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T)
          (u : A →+* T) (v : T →+* Localization.AtPrime Q),
          Algebra.Smooth (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T ∧
          u.comp (algebraMap R A) =
            (algebraMap (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁))) T).comp
              ((algebraMap R₁ (Localization.AtPrime (Q.comap (algebraMap R₁ Λ₁)))).comp σ) ∧
          v.comp u = (algebraMap Λ₁ (Localization.AtPrime Q)).comp (τ.comp f.toRingHom)) →
    CanBeResolved R f q

end Langlands.CommutativeAlgebra.Popescu

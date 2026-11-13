import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Desingularization along a strictly standard element -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.7.3 (07F0). Let `R` be Noetherian, `Λ` an `R`-algebra and
`π ∈ R` with `Ann_R(π) = Ann_R(π²)` and `Ann_Λ(π) = Ann_Λ(π²)`. Let `f : A → Λ` be
an `R`-algebra map with `A` finitely presented and the image of `π` strictly
standard in `A` over `R`. Let `A / π⁸A → C → Λ / π⁸Λ` be a factorization with `C`
finitely presented over `R / π⁸R`. Then there is a factorization `A → B → Λ` with
`B` finitely presented over `R`, `B_π` smooth over `R`, and
`H_{C/(R/π⁸R)} · Λ/π⁸Λ ⊆ √(H_{B/R} Λ) mod π⁸Λ`. -/
def StrictlyStandardDesingularizationStatement : Prop :=
  ∀ (R A Λ : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A] (π : R),
    (∀ x : R, π ^ 2 * x = 0 → π * x = 0) →
    (∀ x : Λ, algebraMap R Λ π ^ 2 * x = 0 → algebraMap R Λ π * x = 0) →
    ∀ f : A →ₐ[R] Λ, IsStrictlyStandard R (algebraMap R A π) →
    ∀ (C : Type u) [CommRing C] [Algebra (R ⧸ Ideal.span {π ^ 8}) C] [Algebra R C]
      [IsScalarTower R (R ⧸ Ideal.span {π ^ 8}) C]
      [Algebra.FinitePresentation (R ⧸ Ideal.span {π ^ 8}) C]
      (u : A →ₐ[R] C) (v : C →ₐ[R] Λ ⧸ (Ideal.span {π ^ 8}).map (algebraMap R Λ)),
      v.comp u = (Ideal.Quotient.mkₐ R _).comp f →
        ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
          Algebra.FinitePresentation R B ∧
            ∃ (g : A →ₐ[R] B) (h : B →ₐ[R] Λ), h.comp g = f ∧
              Algebra.Smooth R (Localization.Away (algebraMap R B π)) ∧
              (singularIdeal (R ⧸ Ideal.span {π ^ 8}) C).map v ≤
                (singularRadical R h).map
                  (Ideal.Quotient.mk ((Ideal.span {π ^ 8}).map (algebraMap R Λ)))

end Langlands.CommutativeAlgebra.Popescu

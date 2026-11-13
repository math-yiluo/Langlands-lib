import Langlands.CommutativeAlgebra.Popescu.Basic

/-! # Factorization when the singular ideal generates the unit ideal -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.2.8 (07EU): let `R → A → Λ` be ring maps with `A` finitely
presented over `R`. If `H_{A/R} Λ = Λ`, then `A → Λ` factors through a smooth
`R`-algebra. -/
def SingularIdealFactorizationStatement : Prop :=
  ∀ (R A Λ : Type u) [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    [Algebra.FinitePresentation R A] (f : A →ₐ[R] Λ),
    (singularIdeal R A).map f = ⊤ →
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
        Algebra.Smooth R B ∧ ∃ (g : A →ₐ[R] B) (h : B →ₐ[R] Λ), h.comp g = f

end Langlands.CommutativeAlgebra.Popescu

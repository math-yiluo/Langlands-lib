import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Descending a smooth factorization from a localization -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.8.3 (07F4), in its strictly standard form: let `A` be a finitely
presented `R`-algebra, `f : A → Λ` an `R`-algebra map and `S ⊆ R` a multiplicative set.
If `S⁻¹A → S⁻¹Λ` factors through a smooth `S⁻¹R`-algebra `B'`, then `f` factors as
`A → B → Λ` with `B` finitely presented over `R` such that some `s ∈ S` maps to a strictly
standard element of `B` over `R`. Here `R'` and `Λ'` are localizations of `R` and `Λ` at
`S`, and an `S⁻¹R`-algebra map `S⁻¹A → B'` is given by the `R`-algebra map `u : A → B'`. -/
def LocalizationStandardDescentStatement : Prop :=
  ∀ (R A Λ R' Λ' : Type u) [CommRing R] [CommRing A] [CommRing Λ] [CommRing R'] [CommRing Λ']
    [Algebra R A] [Algebra R Λ] [Algebra.FinitePresentation R A]
    [Algebra R R'] [Algebra R' Λ'] [Algebra Λ Λ'] [Algebra R Λ']
    [IsScalarTower R R' Λ'] [IsScalarTower R Λ Λ']
    (S : Submonoid R) [IsLocalization S R'] [IsLocalization (Algebra.algebraMapSubmonoid Λ S) Λ']
    (f : A →ₐ[R] Λ)
    (B' : Type u) [CommRing B'] [Algebra R' B'] [Algebra R B'] [IsScalarTower R R' B']
    [Algebra.Smooth R' B'] (u : A →ₐ[R] B') (v : B' →ₐ[R'] Λ'),
    (v.restrictScalars R).comp u = (IsScalarTower.toAlgHom R Λ Λ').comp f →
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
        Algebra.FinitePresentation R B ∧
          ∃ (g : A →ₐ[R] B) (h : B →ₐ[R] Λ), h.comp g = f ∧
            ∃ s ∈ S, IsStrictlyStandard R (algebraMap R B s)

end Langlands.CommutativeAlgebra.Popescu

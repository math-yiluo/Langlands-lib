import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Retracts in which smooth elements become strictly standard -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.3.1 (07CE) combined with Lemma 16.3.7 (07EZ), part (e): let `R` be
Noetherian and `B` a finitely presented `R`-algebra. There is a finitely presented
`R`-algebra `C` with `R`-algebra maps `g : B → C` and `r : C → B`, `r ∘ g = id`, such that
for every `a ∈ B` with `B_a` smooth over `R` some power of `g a` is strictly standard in
`C` over `R`. -/
def StrictlyStandardRetractStatement : Prop :=
  ∀ (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B],
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Algebra.FinitePresentation R C ∧
        ∃ (g : B →ₐ[R] C) (r : C →ₐ[R] B), r.comp g = AlgHom.id R B ∧
          ∀ a : B, Algebra.Smooth R (Localization.Away a) →
            ∃ c : ℕ, IsStrictlyStandard R (g a ^ c)

end Langlands.CommutativeAlgebra.Popescu

import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Uniqueness of the central character of a nonzero operator realization

A nonzero form `f` of an operator realization has a point `x` with `f(x) ≠ 0`. Two central
characters `χ` and `η` give `χ(z) f(x) = f(z x) = η(z) f(x)` for every idele `z`, so they agree
on the ideles and hence on the idele class group.
-/

noncomputable section

set_option autoImplicit false

open scoped NumberField

universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField

namespace OperatorRealization

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

/-- An operator realization with a nonzero vector has at most one central character. -/
theorem hasCentralCharacter_unique [Nontrivial S.Space]
    {χ η : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hχ : S.HasCentralCharacter χ)
    (hη : S.HasCentralCharacter η) : χ = η := by
  obtain ⟨f, hf⟩ := exists_ne (0 : S.Space)
  have hx : ∃ x : AdelicGL F n, ContinuousRationalFunctions.evaluate F n (S.toContinuous f) x ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply S.toContinuous_injective
    rw [map_zero]
    exact Subtype.ext (Subtype.ext (funext h))
  obtain ⟨x, hx⟩ := hx
  ext a
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup (𝓞 F) F) a
  have h1 := S.centralCharacter_evaluate χ hχ f z x
  rw [S.centralCharacter_evaluate η hη f z x] at h1
  exact (mul_right_cancel₀ hx h1).symm
end OperatorRealization

namespace CuspidalOperatorRealization

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

/-- An actual cuspidal realization has at most one central character. -/
theorem hasCentralCharacter_unique {χ η : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ}
    (hχ : T.HasCentralCharacter χ) (hη : T.HasCentralCharacter η) : χ = η :=
  have : Nontrivial T.realization.Space := T.space_nontrivial
  T.realization.hasCentralCharacter_unique hχ hη

end CuspidalOperatorRealization

end Langlands.Automorphic

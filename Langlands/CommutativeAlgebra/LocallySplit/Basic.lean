import Mathlib.LinearAlgebra.Pi

/-! # Locally split modules

A module `M` is *locally split* if the identity of `M` agrees, on any given finite tuple of
elements, with an endomorphism that factors through a finite free module. -/

namespace Langlands.CommutativeAlgebra

/-- `M` is locally split over `R`: for every finite tuple `x` in `M` there are a linear map
`φ : M → R^r` and elements `y : Fin r → M` with `x i = ∑ j, φ (x i) j • y j` for all `i`. -/
def LocallySplit (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ (n : ℕ) (x : Fin n → M), ∃ (r : ℕ) (φ : M →ₗ[R] (Fin r → R)) (y : Fin r → M),
    ∀ i, ∑ j, φ (x i) j • y j = x i

end Langlands.CommutativeAlgebra

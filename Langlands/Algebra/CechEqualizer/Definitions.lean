import Mathlib.RingTheory.TensorProduct.Maps

/-! # Tensor equalizer modules and noetherian model identifications -/

open TensorProduct

namespace Langlands.Algebra.CechEqualizer

section Good

variable {A₀ C₀ C₁ : Type*} [CommRing A₀] [CommRing C₀] [CommRing C₁]
  [Algebra A₀ C₀] [Algebra A₀ C₁] (d : C₀ →ₗ[A₀] C₁)

/-- A module `M` is good for the linear map `d : C₀ → C₁` if every element of `M ⊗ C₀` killed by
`M ⊗ d` has the form `m ⊗ 1`. -/
def Good (M : Type*) [AddCommGroup M] [Module A₀ M] : Prop :=
  ∀ y : M ⊗[A₀] C₀, d.lTensor M y = 0 → ∃ m : M, m ⊗ₜ[A₀] (1 : C₀) = y


end Good

section Model

variable {R A₀ A B C : Type*} [CommRing R] [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A₀] [Algebra R A] [Algebra A₀ A] [IsScalarTower R A₀ A] [Algebra R B] [Algebra A C]

variable (A₀) in
/-- The identification of the base change to `A` of the model `A₀ ⊗[R] B` with `C`, given an
identification `C ≃ A ⊗[R] B`. -/
noncomputable def modelEquiv (ε : C ≃ₐ[A] A ⊗[R] B) : A ⊗[A₀] (A₀ ⊗[R] B) ≃ₐ[A] C :=
  (Algebra.TensorProduct.cancelBaseChange R A₀ A A B).trans ε.symm


end Model

end Langlands.Algebra.CechEqualizer

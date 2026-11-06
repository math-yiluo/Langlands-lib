import Langlands.LinearAlgebra.RestrictedProduct.TensorPiProof
import Mathlib.RingTheory.TensorProduct.Pi

noncomputable section

universe u v w x

open scoped TensorProduct

namespace Langlands.Global

/-- Finite projectivity specializes the published finite-presentation tensor comparison. -/
theorem finiteProjectivePiTensorMap_bijective (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {ι : Type w} (N : ι → Type x) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] :
    Function.Bijective (TensorProduct.piRightHom R R M N) := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  exact RestrictedProduct.tensorPiComparison_proof R M N

/-- The original tensor/product algebra map for arbitrary index sets and finite projective coefficients. -/
def finiteProjectivePiTensorEquiv (R : Type u) (B : Type v)
    [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] {ι : Type w}
    (C : ι → Type x) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)] :
    B ⊗[R] (∀ i, C i) ≃ₐ[B] (∀ i, B ⊗[R] C i) :=
  AlgEquiv.ofBijective (Algebra.TensorProduct.piRightHom R B B C)
    (finiteProjectivePiTensorMap_bijective R B C)

@[simp]
theorem finiteProjectivePiTensorEquiv_tmul (R : Type u) (B : Type v)
    [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] {ι : Type w}
    (C : ι → Type x) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]
    (b : B) (c : ∀ i, C i) (i : ι) :
    finiteProjectivePiTensorEquiv R B C (b ⊗ₜ[R] c) i = b ⊗ₜ[R] c i := rfl

end Langlands.Global

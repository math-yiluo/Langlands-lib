import Langlands.Representation.Tensor.OneFactor
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Quotients of a tensor representation with one acting factor -/

noncomputable section

open scoped TensorProduct

namespace Langlands.BinaryTensor

universe uG uV uW

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Contract the trivially acted second tensor factor against a linear
functional, retaining equivariance for the first-factor action. -/
def firstFactorContraction (ρ : Representation ℂ G V) (φ : Module.Dual ℂ W) :
    (firstFactor ρ W).IntertwiningMap ρ where
  toLinearMap := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ φ.lTensor V
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp

@[simp]
theorem firstFactorContraction_tmul (ρ : Representation ℂ G V)
    (φ : Module.Dual ℂ W) (v : V) (w : W) :
    firstFactorContraction ρ φ (v ⊗ₜ w) = φ w • v := by
  simp [firstFactorContraction]

/-- A functional taking the value one gives a surjective contraction. -/
theorem firstFactorContraction_surjective (ρ : Representation ℂ G V)
    (φ : Module.Dual ℂ W) {w : W} (hw : φ w = 1) :
    Function.Surjective (firstFactorContraction ρ φ) := by
  intro v
  exact ⟨v ⊗ₜ w, by rw [firstFactorContraction_tmul, hw, one_smul]⟩

/-- Any nonzero trivially acted tensor factor admits a choice of actual
surjective equivariant contraction onto the acting factor. -/
def firstFactorQuotient (ρ : Representation ℂ G V) (W : Type uW)
    [AddCommGroup W] [Module ℂ W] [Nontrivial W] :
    {q : (firstFactor ρ W).IntertwiningMap ρ // Function.Surjective q} :=
  Classical.choice (by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hw
    exact ⟨⟨firstFactorContraction ρ φ,
      firstFactorContraction_surjective ρ φ hφ⟩⟩)

end Langlands.BinaryTensor

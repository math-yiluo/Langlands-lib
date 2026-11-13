import Langlands.Representation.Smooth.Factorization.TwoFactorStatement
import Langlands.Representation.TensorProduct.MultiplicityCancellation

/-! # Uniqueness of the two external tensor factors -/

namespace Langlands

universe uG₁ uG₂ uV₁ uV₂ uW₁ uW₂

open Representation

/-- Restricting an equivalence of external tensors to the two groups and
cancelling their trivial multiplicity spaces determines both factors. -/
theorem admissibleProductFactorUniqueness :
    AdmissibleProductFactorUniquenessStatement.{uG₁, uG₂, uV₁, uV₂, uW₁, uW₂} := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ V₁ V₂ W₁ W₂ _ _ _ _ _ _ _ _
    ρ₁ ρ₂ σ₁ σ₂ _ hρ₁ _ hρ₂ _ hσ₁ _ hσ₂ hq
  let := hρ₁
  let := hρ₂
  let := hσ₁
  let := hσ₂
  let : Nontrivial V₁ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G₁) ρ₁.asModule
  let : Nontrivial V₂ := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G₂) ρ₂.asModule
  obtain ⟨q⟩ := hq
  let q₁ : (ρ₁.tprod (Representation.trivial ℂ G₁ V₂)).Equiv
      (σ₁.tprod (Representation.trivial ℂ G₁ W₂)) :=
    Representation.Equiv.mk q.toLinearEquiv (fun g => by
      simpa [Representation.tprod_apply, Representation.trivial] using q.isIntertwining' (g, 1))
  let q₂ : ((Representation.trivial ℂ G₂ V₁).tprod ρ₂).Equiv
      ((Representation.trivial ℂ G₂ W₁).tprod σ₂) :=
    Representation.Equiv.mk q.toLinearEquiv (fun g => by
      simpa [Representation.tprod_apply, Representation.trivial] using q.isIntertwining' (1, g))
  exact ⟨TensorMultiplicity.nonempty_equiv_of_tensor_trivial ρ₁ σ₁ q₁,
    TensorMultiplicity.nonempty_equiv_of_tensor_trivial ρ₂ σ₂
      (((Representation.TensorProduct.comm ρ₂ (Representation.trivial ℂ G₂ V₁)).trans q₂).trans
        (Representation.TensorProduct.comm (Representation.trivial ℂ G₂ W₁) σ₂))⟩

end Langlands

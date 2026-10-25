import Langlands.Representation.Smooth.Factorization.RestrictedTensorStatement
import Langlands.Representation.RestrictedTensor.LocalSeparation
import Langlands.Representation.TensorProduct.MultiplicityCancellation

/-! # Uniqueness of the local factors of constructed restricted tensors -/

noncomputable section
open scoped Classical TensorProduct

universe uI uG uV uW

namespace Langlands

open RestrictedTensor

/-- A global equivalence between constructed restricted tensors of irreducible
local factors determines the equivalence class of each local factor. -/
theorem restrictedTensorFactorUniqueness :
    RestrictedTensorFactorUniquenessStatement.{uI, uG, uV, uW} := by
  intro ι G _ _ _ _ _ _ H V W _ _ _ _ ρ σ E E' r s hr hs _ hρ hσ _ _ hq i
  rcases hq with ⟨q⟩
  let : ∀ j, (ρ j).IsIrreducible := fun j => (hρ j).2
  let : (σ i).IsIrreducible := (hσ i).2
  let : ∀ j, Nontrivial (V j) := fun j =>
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (G j)) (ρ j).asModule
  let : Nontrivial (LocalTensorTail (K := ℂ) E i r.family) :=
    localTensorTail_nontrivial E i r.family r.family_nonzero
  let qLocal : Representation.Equiv
      ((productRepresentation H ρ E r hr).comp (localInsertion H i))
      ((productRepresentation H σ E' s hs).comp (localInsertion H i)) :=
    Representation.Equiv.mk q.toLinearEquiv
      (fun g => q.isIntertwining' (localInsertion H i g))
  exact TensorMultiplicity.nonempty_equiv_of_tensor_trivial (ρ i) (σ i)
    (((productLocalTensorSeparation H ρ E r hr i).symm.trans qLocal).trans
      (productLocalTensorSeparation H σ E' s hs i))

end Langlands

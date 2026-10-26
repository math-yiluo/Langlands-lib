import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Unitary.Basic

/-!
# Invariant positive forms on finite external tensor products

This module states the algebraic positive-form construction on the existing
indexed tensor representation. The proposition includes its values on pure
tensors and requires positive definiteness on the entire tensor carrier.
-/

namespace Langlands.FiniteTensor

universe uI uG uV

/-- Given invariant positive forms on a finite family of actual complex
representations, the actual external tensor product admits an invariant positive
form whose value on pure tensors is the product of the factor values. -/
def InvariantPositiveFormStatement : Prop :=
  ∀ (ι : Type uI) [Fintype ι]
    (G : ι → Type uG) [∀ i, Group (G i)]
    (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i))
    (b : ∀ i, Langlands.InvariantPositiveForm (ρ i)),
    ∃ bT : Langlands.InvariantPositiveForm (external ρ),
      ∀ v w : ∀ i, V i,
        bT.inner (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w) =
          ∏ i, (b i).inner (v i) (w i)

end Langlands.FiniteTensor

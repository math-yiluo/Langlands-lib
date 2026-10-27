import Mathlib.Basic.Complex.Basic
import Langlands.Representation.Tensor.SmoothDual

/-!
# Injectivity of the finite smooth-dual tensor map

This proposition states a remaining proof obligation for the published canonical
map. It uses the supplied factor topologies and their actual product topology.
-/

namespace Langlands.FiniteTensor

universe uI uG uV

/-- For every finite family of complex representations of topological groups,
the canonical map from the tensor of the factor smooth duals to the smooth dual
of the external tensor product is injective. This is a statement, not a proof. -/
def SmoothDualTensorInjectivityStatement : Prop :=
  ∀ (ι : Type uI) [Finite ι]
    (G : ι → Type uG) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i)),
    Function.Injective (smoothDualTensorMap ρ)

end Langlands.FiniteTensor

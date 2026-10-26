import Mathlib.Basic.Complex.Basic
import Langlands.Representation.Tensor.SmoothDual

/-!
# Surjectivity of the finite smooth-dual tensor map

This proposition states a remaining proof obligation for the published canonical
map. It uses the supplied factor topologies and their actual product topology.
-/

namespace Langlands.FiniteTensor

universe uI uG uV

/-- For finite families of admissible complex representations with factorwise
compact-open cofinality, the canonical tensor map onto the smooth dual of the
external tensor product is surjective. This is a statement, not a proof. -/
def SmoothDualTensorSurjectivityStatement : Prop :=
  ∀ (ι : Type uI) [Finite ι]
    (G : ι → Type uG) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (G i) (V i)),
    (∀ i, IsAdmissible (ρ i)) →
    (∀ i (K : OpenSubgroup (G i)), ∃ L : OpenSubgroup (G i),
      IsCompact (L : Set (G i)) ∧ L ≤ K) →
    Function.Surjective (smoothDualTensorMap ρ)

end Langlands.FiniteTensor

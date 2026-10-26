import Langlands.Representation.Induction.FiniteProductTensor
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Compactness.LocallyCompact

/-! Compact-quotient bijectivity of the canonical finite-product induction map. -/

namespace Langlands.Induction

universe uK uI uG uV

/-- The actual pointwise tensor map is bijective for every finite family with
compact left quotients over weakly locally compact nonarchimedean groups.
This proposition includes the empty family and arbitrary inducing actions. -/
def FiniteProductTensorBijectiveTheorem : Prop :=
  ∀ (k : Type uK) [Field k] (ι : Type uI) [Finite ι]
    (G : ι → Type uG) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanGroup (G i)] [∀ i, WeaklyLocallyCompactSpace (G i)]
    (P : ∀ i, Subgroup (G i)) [∀ i, CompactSpace (LeftQuotient (P i))]
    (V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (σ : ∀ i, Representation k (P i) (V i)),
      Function.Bijective (finiteProductTensorMap P σ)

end Langlands.Induction

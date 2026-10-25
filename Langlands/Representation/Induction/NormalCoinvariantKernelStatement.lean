import Langlands.Representation.Induction.Definitions
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Basic.Complex.Basic

namespace Langlands.Induction

universe uG uV

/-- The normal-subgroup relation span in compact induction is detected pointwise
by the relation span in the inducing representation. -/
def CompactInductionNormalCoinvariantKernel : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (H N : Subgroup G) [N.Normal],
      IsClosed (H : Set G) → IsClosed (N : Set G) → N ≤ H →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (sigma : Representation ℂ H V), Langlands.IsSmooth sigma →
        ∀ f : CompactFunctions H sigma,
          (f ∈ Representation.Coinvariants.ker
            ((compactInduced H sigma).comp N.subtype)) ↔
          (∀ g : G, eval H sigma f.val g ∈ Representation.Coinvariants.ker
            (sigma.comp (N.subgroupOf H).subtype))

end Langlands.Induction

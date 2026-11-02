import Langlands.Representation.Plancherel.UnramifiedCharacters
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Topology and compact-subgroup properties of the common norm kernel

A derived prerequisite for the valuation quotient and unramified-character
tori. It assumes continuity of the actual given norm characters, rather than
any conclusion about their common kernel.
-/

open scoped NNReal

namespace Langlands.Plancherel

universe uG uI

/-- The common kernel of continuous positive characters of a weakly locally
compact nonarchimedean group is open and closed, contains every compact
subgroup and contains the abstract group commutator subgroup. -/
def CommonNormKernelTopologyStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (I : Type uI) (ν : I → (G →* ℝ≥0ˣ)),
    (∀ i, Continuous (ν i)) →
      IsOpen (commonNormKernel ν : Set G) ∧
      IsClosed (commonNormKernel ν : Set G) ∧
      (∀ K : Subgroup G, IsCompact (K : Set G) → K ≤ commonNormKernel ν) ∧
      _root_.commutator G ≤ commonNormKernel ν

end Langlands.Plancherel

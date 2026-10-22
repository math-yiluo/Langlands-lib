import Langlands.Weil.Pullback

/-! # The open-inertia topology and its uniqueness, stated for later proof. -/

namespace Langlands.Weil

universe u

/-- The product-subtype topology is a group topology with inertia open and
embedded with its given topology. These requirements uniquely determine it. -/
def TopologyProperties : Prop :=
  ∀ (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (φ : Γ →ₜ* ProfiniteIntegers),
    let originalTopology : TopologicalSpace (Pullback φ) := inferInstance
    let originalInertiaTopology : TopologicalSpace (inertia φ) := inferInstance
    IsTopologicalGroup (Pullback φ) ∧
    Topology.IsOpenEmbedding (inertiaInclusion φ) ∧
    IsOpen (inertiaSubgroup φ : Set (Pullback φ)) ∧
    ∀ t : TopologicalSpace (Pullback φ),
      @IsTopologicalGroup (Pullback φ) t inferInstance →
      @Topology.IsOpenEmbedding (inertia φ) (Pullback φ) originalInertiaTopology t
        (inertiaInclusion φ) →
      t = originalTopology

end Langlands.Weil

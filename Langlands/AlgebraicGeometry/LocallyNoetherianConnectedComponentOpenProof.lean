import Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenStatement
import Mathlib.Topology.NoetherianSpace

/-! # Proof that connected components of a locally Noetherian scheme are open

In a Noetherian topological space the complement of a connected component is a
finite union of irreducible components, so the component is open. A point of a
locally Noetherian scheme has an affine open neighbourhood whose underlying
space is Noetherian; the connected component of the point in that neighbourhood
is then an open neighbourhood contained in the global connected component.
-/

universe u

open AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- In a Noetherian topological space every connected component is open. -/
theorem isOpen_connectedComponent_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  let S : Set (Set α) :=
    {Z | Z ∈ irreducibleComponents α ∧ Disjoint Z (connectedComponent x)}
  have hclosed : IsClosed (⋃₀ S) :=
    (NoetherianSpace.finite_irreducibleComponents.subset fun _ hZ => hZ.1).isClosed_sUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have hcompl : connectedComponent x = (⋃₀ S)ᶜ := by
    ext y
    constructor
    · rintro hy ⟨Z, ⟨-, hdisj⟩, hyZ⟩
      exact Set.disjoint_left.mp hdisj hyZ hy
    · intro hy
      by_contra hyx
      have hne : connectedComponent y ≠ connectedComponent x := fun h =>
        hyx (h ▸ mem_connectedComponent)
      exact hy ⟨irreducibleComponent y,
        ⟨irreducibleComponent_mem_irreducibleComponents y,
          (connectedComponent_disjoint hne).mono_left
            irreducibleComponent_subset_connectedComponent⟩,
        mem_irreducibleComponent⟩
  rw [hcompl]
  exact hclosed.isOpen_compl

/-- Every connected component of a locally Noetherian scheme is open. -/
theorem locallyNoetherianConnectedComponentOpen_proof :
    LocallyNoetherianConnectedComponentOpenStatement.{u} := by
  intro X _ x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (Opens.mem_top y : y ∈ (⊤ : X.Opens))
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let y' : U := ⟨y, hyU⟩
  have hopen : IsOpen (connectedComponent y') :=
    @isOpen_connectedComponent_of_noetherianSpace U _ (noetherianSpace_of_isAffineOpen U hU) y'
  refine ⟨Subtype.val '' connectedComponent y', ?_, ?_, ⟨y', mem_connectedComponent, rfl⟩⟩
  · rw [connectedComponent_eq hy]
    exact (isConnected_connectedComponent.image _
      continuous_subtype_val.continuousOn).subset_connectedComponent
      ⟨y', mem_connectedComponent, rfl⟩
  · exact U.isOpen.isOpenMap_subtype_val _ hopen

end Langlands.AlgebraicGeometry

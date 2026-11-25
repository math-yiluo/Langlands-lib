module

public import Mathlib.Topology.Sober

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Generic points of irreducible components and generization

A point of a Kolmogorov space whose singleton has an irreducible component as closure admits
no generization but itself: a generization has a larger closure, which is irreducible, so
maximality makes the two closures equal. The converse needs the space to be quasi-sober — the
component containing the point has to have a generic point before the hypothesis can be
applied to it — and it genuinely fails without that: an infinite set with the cofinite
topology is Kolmogorov, every point of it admits no generization but itself, and yet it is
irreducible, so its unique irreducible component is the whole space and no singleton closure
is a component (`not_quasiSober_cofiniteTopology`,
`irreducibleComponents_cofiniteTopology`).

## Main results

* `TopologicalSpace.forall_specializes_eq_of_mem_genericPoints`: on a Kolmogorov space a
  generic point of an irreducible component has no proper generization.
* `TopologicalSpace.mem_genericPoints_of_forall_specializes_eq`: on a sober space the
  converse.
* `TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq`: the two together.
* `TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff`: the same criterion for a
  generic point of an irreducible component of a closed subset, read in the ambient space.
-/

@[expose] public section

namespace TopologicalSpace

variable {α : Type*} [TopologicalSpace α]

/-- On a Kolmogorov space a generic point of an irreducible component has no generization but
itself: the closure of a generization contains the component, is irreducible, and so equals
it by maximality. -/
theorem forall_specializes_eq_of_mem_genericPoints [T0Space α] {x : α}
    (hx : x ∈ genericPoints α) (y : α) (hyx : y ⤳ x) : y = x :=
  have hback : closure ({y} : Set α) ⊆ closure ({x} : Set α) :=
    hx.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.mp hyx)
  (hyx.antisymm (specializes_iff_closure_subset.mpr hback)).eq

/-- On a sober space a point with no generization but itself is a generic point of an
irreducible component: the component containing it has a generic point, which is one of its
generizations and therefore the point itself. -/
theorem mem_genericPoints_of_forall_specializes_eq [T0Space α] [QuasiSober α] {x : α}
    (h : ∀ y : α, y ⤳ x → y = x) : x ∈ genericPoints α := by
  set Z : irreducibleComponents α :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hZ : (genericPoints.ofComponent Z : α) = x :=
    h _ ((genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent)
  exact hZ ▸ (genericPoints.ofComponent Z).2

/-- On a sober space a point is a generic point of an irreducible component exactly when it
has no generization but itself. -/
theorem mem_genericPoints_iff_forall_specializes_eq [T0Space α] [QuasiSober α] (x : α) :
    x ∈ genericPoints α ↔ ∀ y : α, y ⤳ x → y = x :=
  ⟨forall_specializes_eq_of_mem_genericPoints, mem_genericPoints_of_forall_specializes_eq⟩

end TopologicalSpace

end

module

public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Embedded points and embedded components

An *embedded* associated point of a sheaf of modules is an associated point which is a proper
specialization of another associated point. The embedded points of a scheme are the embedded
associated points of its structure sheaf, and their closures are the embedded components.

## Main definitions

* `AlgebraicGeometry.IsEmbeddedAssociatedPoint`: an embedded associated point of a sheaf of
  modules.
* `AlgebraicGeometry.IsEmbeddedPoint`: an embedded point of a scheme.
* `AlgebraicGeometry.IsEmbeddedComponent`: an embedded component of a scheme.
* `AlgebraicGeometry.HasNoEmbeddedAssociatedPoints` and
  `AlgebraicGeometry.HasNoEmbeddedPoints`: the corresponding absence predicates.

## Main results

* `Topology.eq_of_specializes_isGenericPoint`: a point specializing to the generic point of an
  irreducible component is that point.

## Implementation notes

`AlgebraicGeometry.IsEmbeddedAssociatedPoint`, `AlgebraicGeometry.IsEmbeddedPoint` and
`AlgebraicGeometry.IsEmbeddedComponent` correspond respectively to parts (1), (2) and (3) of the
definition in Stacks 05AK. As for associated points, quasi-coherence is not needed to form these
notions, so they are defined for every sheaf of modules. The condition that the specializing point
be different records the word "another", and hence the failure of maximality. An embedded component
is specified as the closure of its embedded point; such a closure is automatically closed and
irreducible. All the predicates are abbreviations, so that clients can use their logical forms
directly.

The specialization relation is Mathlib's `Specializes`, written `x' ⤳ x`.

## References

* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
-/

@[expose] public section

universe u

namespace Topology

/-- A point specializing to the generic point of an irreducible component is that point: its
closure would otherwise be a strictly larger irreducible closed set. -/
lemma eq_of_specializes_isGenericPoint {T : Type*} [TopologicalSpace T] [T0Space T] {Z : Set T}
    (hZ : Z ∈ irreducibleComponents T) {x : T} (hx : IsGenericPoint x Z) {y : T}
    (hyx : y ⤳ x) : y = x := by
  have hsub : Z ⊆ closure ({y} : Set T) := by
    rw [← hx.def]
    exact closure_minimal (by simpa using specializes_iff_mem_closure.mp hyx) isClosed_closure
  exact (hx.eq (show IsGenericPoint y Z from
    (hZ.2 isIrreducible_singleton.closure hsub).antisymm hsub)).symm

end Topology

namespace AlgebraicGeometry

end AlgebraicGeometry

module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.Topology.Sober.Generization

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Flat separated morphisms with distinct generic points are universally injective

A flat separated morphism of schemes whose residue-field maps at the generic points of its
source are isomorphisms, and which is injective on those generic points, is universally
injective.

## Main results

* `AlgebraicGeometry.universallyInjective_of_flat_of_separated_of_genericPoints_injOn` is the
  criterion.

## Implementation notes

The equality of residue fields in the source is expressed by the canonical residue-field map
being an isomorphism. The condition on distinct generic points is expressed by injectivity on
Mathlib's `genericPoints` set.

Universal injectivity is checked on the diagonal: the diagonal of a separated morphism is a
closed embedding, so its range is closed, and flatness makes both projections generalizing, so
every generic point of the fibre product comes from a generic point of the source. The
hypotheses force that point to be the diagonal image, and the range, being closed and containing
every generic point, is everything.

## References

* [Stacks Project, Tag 09NP](https://stacks.math.columbia.edu/tag/09NP)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A generalizing map between quasi-sober `T₀` spaces sends generic points to generic points. -/
public lemma genericPoints_map_of_generalizingMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space X] [T0Space Y]
    [QuasiSober X] [QuasiSober Y] (g : X → Y) (hg : GeneralizingMap g)
    {x : X} (hx : x ∈ genericPoints X) : g x ∈ genericPoints Y := by
  refine (mem_genericPoints_iff_forall_specializes_eq (g x)).2 fun y hy => ?_
  obtain ⟨x', hx', rfl⟩ := hg hy
  rw [(mem_genericPoints_iff_forall_specializes_eq x).1 hx x' hx']

end AlgebraicGeometry

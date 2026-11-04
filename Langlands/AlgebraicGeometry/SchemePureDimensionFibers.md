# The pure-dimension component of the geometric fibre property

This construction isolates the dimension condition in the final property
of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The decomposition and transport maps are internal derived constructions
for comparing actual pullback models; Conrad does not name this separate
predicate or these maps.

In `Langlands.AlgebraicGeometry.SchemeFiberGeometry`, the morphism property
`HasPureDimensionFibers d` requires `HasPureDimension (f.fiber y) d` for
every actual target point y, in arbitrary universe u. Thus every irreducible
component of every actual residue-field fibre has dimension d. Empty fibres
satisfy it vacuously. No geometric connectedness, nonemptiness or finiteness
hypothesis is part of this dimension-only definition.

`precompFiberHomeomorph` identifies the actual fibre of `e.hom ≫ f` at z
with that of f at z, for a scheme isomorphism e on the source.
`postcompFiberHomeomorph` identifies the actual fibre of `f ≫ e.hom` at z
with that of f at `e.inv z`, for a scheme isomorphism e on the target.
Both constructions use Mathlib's `Scheme.Hom.fiberHomeo`, which identifies
a scheme-theoretic fibre with the inverse image of a singleton in the
underlying topological space. The first restricts the source
homeomorphism to these subsets. The second identifies two equal subsets
using the inverse target homeomorphism. These are homeomorphisms of
underlying fibre spaces; no isomorphism of fibre schemes is claimed.

The `RespectsIso` instance for the dimension property transports pure
dimension along these homeomorphisms using `HasPureDimension.of_homeomorph`.
`nonemptyGeometricallyConnectedPureDimensionFibers_eq` proves equality of
the full property with the intersection of Mathlib geometric connectedness
and `HasPureDimensionFibers d`; it is precisely the existing fibrewise
comparison with the new name for its dimension conjunct. Their intersection
therefore supplies a `RespectsIso` instance for the full property.
Mathlib geometric connectedness respects isomorphisms because it is
stable under base change; the implementation invokes that implication
explicitly in the same universe `u`.
The final two equivalences apply these instances to an actual isomorphism
in the arrow category, allowing both source and target to change.

All these intrinsic comparisons hold for arbitrary scheme morphisms.
They do not assert invariance under field extension or general base change,
constructibility of fibre loci, or descent along filtered ring colimits.
Those are separate obligations of the source theorem.

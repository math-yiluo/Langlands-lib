# Actual split-torus actions in corepresented coordinates

This internal construction expresses an actual automorphic action on the
original algebra-point functor as the `Corepresented.TorusAction` used by the
published coordinate grading and weight subgroup constructions. It works over
an arbitrary commutative base ring, in arbitrary universe `u`.

Given an actual action of `H` on `G` and a group-scheme isomorphism from `H`
to the split torus indexed by a finite type `I`, `torusPoint` takes a family
of units to the corresponding actual point of `H`. Its identity,
multiplication and algebra-change laws follow from the published split-torus
point equivalence and its naturality. `toCorepresentedTorusAction` then uses
the original action morphism on these points. Its laws are the original
automorphic action laws. The point recovery theorem shows that this describes
every original acting point on every algebra, without changing the action.

For affine `G`, `TorusActionCoordinates.corepresentation` reuses the existing
corepresentation through `Lie.coordinateIso G`. Its coordinate map is exactly
`Lie.pointCoordinates G`. The published model isomorphism recovers `G` as an
actual group scheme, rather than only as a scheme or a collection of points.

The provenance is internal composition of existing Library constructions:
actual affine points, split-torus algebra points, automorphic action laws,
the affine coordinate presentation and the affine model recovery isomorphism.
No smoothness, connectedness, Lie-image, semigroup realization or structural
unipotence theorem is proved here.

# Geometry of exact outer-isomorphism orbits

Worker 592. This is internal, derived material for the relative automorphism
geometry in Conrad, *Reductive group schemes* (2014), Theorem 7.1.9(1).
It assumes an actual `OuterIsomorphismScheme`; it does not assert existence
of an isomorphism representative or of its outer quotient.

The exact all-test orbit condition identifies the product of the acting group
with any family of representatives as the pullback of the class map over that
family's class. The Lean proof constructs the pullback lift from the unique
difference point and verifies both projections and uniqueness. Pulling back
along the class map itself and applying fpqc descent transfers any stable
morphism property with fpqc target descent from the acting group to the
class map. In particular the class map is affine, smooth, or locally of finite
presentation when the acting group has the respective property.

For a family over the base itself, `orbitMap` is the existing `pointOrbit`. It is the pullback over its
outer-class section. A section of a separated outer parameter is a closed
immersion, so the orbit map is a closed immersion. Finally the map obtained
by positively twisting the family is the orbit map precomposed with group
inversion. Inversion is an isomorphism, and hence that positive twist also
classifies a closed immersion. The canonical action uses inverse
precomposition; the inversion calculation preserves this convention.

These assertions hold over every base scheme, in every universe, on all
relative scheme tests. No finiteness, affineness, or connectedness condition
on the outer parameter is used. Separatedness is required only for the
closed-orbit assertions.

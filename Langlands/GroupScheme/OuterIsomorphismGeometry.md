# Geometry of exact outer-isomorphism orbits

This is internal, derived material for the relative automorphism
geometry in Conrad, *Reductive group schemes* (2014), Theorem 7.1.9(1).
It assumes an actual `OuterIsomorphismScheme`; it does not assert existence
of an isomorphism representative or of its outer quotient.

The exact all-test orbit condition identifies the product of the acting group
with any family of representatives as the pullback of the class map over that
family's class. The invariance and exact orbit fields are passed to
`SchemeAction.isPullback_of_point_of_exact_orbits`, the same lemma used
for represented action quotients. Pulling back along the class map itself
and applying fpqc descent transfers any stable morphism property with
fpqc target descent from the acting group to the class map. In particular
the class map is affine, smooth, or locally of finite presentation when
the acting group has the respective property.

For a family over the base itself, `orbitMap` is the existing `pointOrbit`.
The product with the base is isomorphic to the acting group, which transports
the family pullback to the square over the outer-class section.
`pointOrbit_isClosedImmersion` gives the closed immersion when the outer
parameter is separated. The positive twist is the orbit map precomposed
with group inversion, because the canonical action uses inverse
precomposition. Inversion is an isomorphism, so the positive twist also
classifies a closed immersion.

These assertions hold over every base scheme, in every universe, on all
relative scheme tests. No finiteness, affineness, or connectedness condition
on the outer parameter is used. Separatedness is required only for the
closed-orbit assertions.

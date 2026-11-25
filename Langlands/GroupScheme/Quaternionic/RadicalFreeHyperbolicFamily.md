# Hyperbolic families for forms with zero quadratic radical

This internal extension of `QuadraticHyperbolicFamily` replaces the invertibility
of the polar matrix by `IsRadicalFreeQuadratic`. It retains the quotient-valued
quadratic-form convention over every field and division algebra with an
involution of the first kind, in arbitrary characteristic.

`exists_polar_dual_family_of_radicalFree` constructs a polar-dual family for a
linearly independent family lying in a totally singular subspace. The proof
shows that the polar functionals jointly map onto the coordinate space. A
hypothetical nonzero functional annihilating their image would give a linear
combination of the original vectors orthogonal to every vector. That linear
combination is singular because it lies in the supplied totally singular
subspace. Zero quadratic radical makes it zero, contradicting linear
independence and the nonzero functional.

`exists_isHyperbolicFamily_of_radicalFree` takes a basis of a totally singular
subspace of dimension the quadratic Witt index, chooses its polar-dual family,
and corrects that family by a triangular combination of the original basis.
The correction makes all its vectors singular and mutually polar orthogonal,
while preserving the dual pairing. This is the same implemented algebra as
`exists_isHyperbolicFamily` in `QuadraticHyperbolicFamily`; only its dual-family
input changes. No smoothness of an isometry group is assumed or concluded.

The provenance is internal: these are extensions of the Library's explicit
polar-duality and triangular-correction arguments, using its previously proved
quadratic-radical predicate. No new translation of a literature claim is made.

`radicalFreeHyperbolicFamily` chooses the two families and packages them with
their `IsHyperbolicFamily` proof. Its index type is exactly
`Fin (quadraticWittIndex q)`.

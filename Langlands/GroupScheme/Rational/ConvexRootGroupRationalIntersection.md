# Rational intersection from normalization

This internal supporting reduction concerns a connected reductive group over
a field, a maximal split torus, and two individually convex subsets of its
full relative root set. Three supplied morphisms exhibit the groups of the
two subsets and their common roots. Assume that the intersection of the first
two all-test subgroup functors normalizes the third on every test scheme.
Also assume that the chosen torus is an absolute maximal torus and that the
common-root group has rational maximal-torus conjugacy. Then the intersection
of the images of the first two groups on rational points equals the image of
the common-root group.

Minimality puts the common-root group into each of the first two groups.
Its containment of the whole-torus centralizer factors the chosen torus
through it; absolute maximality descends to this factor. The overgroup
normalizer factorization reduces rational containment to torus-normalizing
points that remain in both groups. The convex normalizer/Weyl intersection
formula puts these points in the common-root group. Multiplication with the
other factor gives the forward inclusion. Minimality already gives the
reverse inclusion.

The algebraically closed specialization requires the common-root group to
be smooth, affine and connected. Finite Galois splitting makes every torus
split over this field, so maximal split tori are absolute maximal tori. The
published maximal-torus conjugacy theorem supplies rational conjugacy for
the common-root group. The all-test normalization premise is retained.

`ConvexRootGroupRationalIntersectionStatement` packages the first assertion
uniformly over all fields in universe `u`, retaining absolute maximality,
rational maximal-torus conjugacy, and the all-test normalization hypothesis.
`convexRootGroupRationalIntersection` proves this proposition by the reduction
above. The algebraically closed specialization is provided separately.

The result is an internal derivation from the normalizer factorization and
convex normalizer/Weyl bridge. It does not assert normalization, field-extension
compatibility, or equality on arbitrary reduced test schemes. Those are
separate inputs to the exact group-intersection proof.

# Vertex fields and actual fundamental-weight orbit sums

This internal module starts with `d : TitsIndexData G` for an affine, locally
finite type group scheme `G` over an arbitrary field. It uses the finite
vertex orbits and fundamental-weight sums constructed in
`CenterOrbitCharacters` and `StarOrbitWeights`. The results apply in every
characteristic and to every Dynkin type.

The results about actual integral fundamental weights assume
`IsSimplyConnected G`. Simple connectedness supplies full integral
coroot span, so the dual basis gives a distinct integral character for
each simple vertex. By star covariance of this basis, the transported
weight at `a` equals the weight at `b` precisely when the corresponding
star translate of `a` equals `b`. The vertex-field stabilizer theorem
then shows that an absolute Galois automorphism fixes the fundamental
weight exactly when it fixes the vertex field pointwise.
This refers to the star action on the integral weight lattice in the
original separable closure.

For general `d : TitsIndexData G`, `starVertexCosetOrbitEquiv a` identifies
the left cosets of the actual vertex stabilizer with the vertices of its
full star orbit. The implementation uses the ordinary orbit-stabilizer
equivalence for the action `d.star`,
then identifies its orbit predicate with the finite-orbit membership
predicate. At the coset represented by `sigma` it gives `d.star sigma a`.
The stabilizer need not be normal, and the associated field need not be
Galois or cyclic.

The quotient is finite because the actual vertex orbit is finite. The
published degree/index theorem and this equivalence identify the degree of
the actual vertex field with the number of orbit vertices. Since the orbit
contains its original vertex, the degree is positive, so the field is a
finite-dimensional extension. The imported vertex-field construction
supplies separability. The coset equivalence, quotient finiteness and
field-degree and finite-dimensionality results apply to general index data.

With `IsSimplyConnected G`, `sum_starVertexCosets_eq_absoluteOrbitWeight`
reindexes the finite sum of actual fundamental weights through this
equivalence. The coset sum counts each vertex weight once and equals
`absoluteOrbitWeight`.
The theorem accepts any `Fintype` presentation of the quotient, whose
finiteness has been proved, so the conclusion is independent of its
enumeration.

The proofs use the published actual fundamental-weight basis, its star
covariance, the actual fixed-field/stabilizer equality and Mathlib's
orbit-stabilizer theorem. The stabilizer comparison concerns the fundamental
weight on the ambient torus.

The injectivity of the fundamental characters and the finite-dimensional instance for each vertex field come from the vertex-field weight construction. [Star vertex field weights](StarVertexFieldWeights.md)

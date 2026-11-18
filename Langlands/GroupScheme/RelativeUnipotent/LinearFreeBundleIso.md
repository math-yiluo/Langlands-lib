# Actual module isomorphisms from positive-weight vector-group isomorphisms

This internal prerequisite for the relative radical filtration converts an
actual polynomial vector-group isomorphism, equivariant for a common positive
scalar power on all coefficient algebras, into an actual isomorphism of its
original finite free module sheaves.

The existing arbitrary-ring weight-linearity construction supplies a base-ring
linear equivalence from the forward scalar-weight hypothesis alone. Its forward
matrix is exactly the original map's weight matrix. Its actual inverse linear
equivalence supplies an inverse rectangular matrix. Mapping both matrices through
the actual inverse `Scheme.ΓSpecIso` gives global-section matrices; their inverse
relations construct the actual free-sheaf isomorphism.

`moduleIso_hom` retains the original forward weight matrix.
`moduleIso_sections` proves on every scheme test that the original group
isomorphism and the constructed module map act identically in the same canonical
free-vector section coordinates. The original group map is first identified
with its matrix map, and the actual all-test matrix/sheaf compatibility is applied.

The ranks are independent and may be zero, and the base ring may be arbitrary.
The actual group isomorphism, positive degree and forward all-algebra scalar-weight
condition are explicit inputs. In the filtration application, the original
quotient comparison and its weight condition still have to supply these inputs.
No overlap gluing, cocycle or global vector-bundle descent is asserted here.

Provenance: an internal derivation from arbitrary-ring positive-weight rigidity
and the actual free-module matrix construction.

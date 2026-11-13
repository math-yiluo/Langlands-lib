# Type C distinguished vertices from actual restriction coordinates

Author: Worker 244 for Task 6244.

`HasTypeCRestrictionCoordinates d n degree r` is an internal interface for
the remaining geometric construction. It requires a numbering of the actual
simple vertices whose actual Cartan matrix is `CartanMatrix.C n`, an additive
equivalence from the character lattice of the actual maximal split torus to
`Fin r → ℤ`, and equality of the actual simple-root restrictions with the
explicit repeated-block restrictions in `TypeCBlockWeights`.

It assumes neither the distinguished-vertex conclusion nor the existence
of such coordinates for an antihermitian group.

The first helper computes the distinguished vertices of an index supplied
with those coordinates. An additive equivalence detects zero, so the
integer calculation applies to the actual root restrictions.

`TitsIndexEquiv.typeC_numbering_eq` compares two numberings whose matrices
are type C. The vertex equivalence preserves the Cartan matrix, and
`CartanCNumbering.unique` forces the two numberings to agree. The next
helper transports a computed marked set using the actual equivalence's
zero-vertex comparison.

Finally, `typeC_distinguished_of_coordinates` applies the published
`titsIndexIndependence` theorem. It computes the marked set in any supplied
convenient index with these coordinates and transports it to the given
index and the given numbering. It retains positive `degree`,
`r * degree ≤ n`, and `2 ≤ n`.

Provenance: internal. The interface and transport lemmas are derived from
the published definitions of actual Tits indices, their proved independence,
and the elementary Cartan and block-weight helpers. They are a conditional
reduction of Task 6244; constructing these coordinates from its original
antihermitian hypotheses is still required.

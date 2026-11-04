# A Lie element belongs to its own centralizer tangent space

This internal supporting argument proves that every actual tangent element of
an affine locally finite type group over an arbitrary field belongs to the
tangent submodule of its actual all-test adjoint centralizer. It requires no
smoothness, connectedness, semisimplicity or characteristic hypothesis.

The proof uses the published closed linear embedding of the group. In that
faithful matrix representation the tangent point is `1 + epsilon*M`. Its
conjugation on the constant lift of `M` adds the epsilon coefficient
`M*M - M*M`, which vanishes. Naturality of the actual kernel maps reflects
this stabilizer equation through the closed embedding. The published affine
centralizer criterion promotes that equation to all-test membership.

The canonical tangent factor uses representability to factor the original
dual-number point through a representative of the centralizer. Monicity
reflects its reduction to the identity, and the factor maps back to the
original tangent element.

This is derived from existing actual-point, representation differential and
representability APIs. It supplies a local adapter for the no-torus argument;
it does not establish centralizer smoothness or the parent unipotence theorem.

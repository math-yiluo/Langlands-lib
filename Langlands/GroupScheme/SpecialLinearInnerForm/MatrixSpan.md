# Special linear matrices span the matrix algebra

This is an internal algebraic lemma for the descent construction of inner forms
of special linear groups. It is derived directly from elementary matrices; it
does not assert any classification theorem.

`span_specialLinear` states that, for every finite index type and commutative
coefficient ring, the matrices of determinant one span the entire matrix module.
For distinct indices, subtracting the identity from a transvection gives an
off-diagonal matrix unit. A diagonal unit is
`T_ij T_ji - T_ij - T_ji + I`. For a singleton index type the identity already
supplies the diagonal unit. The empty index type is covered by the empty matrix
expansion. Finally every matrix is the sum of its single-entry matrices.

`linearMap_ext_specialLinear` applies span induction to deduce that two linear
maps out of the matrix module are equal if they agree on determinant-one
matrices. These arguments impose no characteristic restriction.

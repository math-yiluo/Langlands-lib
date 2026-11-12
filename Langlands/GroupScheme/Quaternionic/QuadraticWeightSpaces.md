# Singular division-algebra weight spaces

This internal derived module studies a family of `D`-linear operators preserving
a quotient-valued quadratic form and having prescribed scalar eigenvalues in
`K`. Their common weight spaces are `D`-subspaces because the central scalars
commute with `D`. Distinct scalar functions give disjoint weight spaces.

The central-scalar sesquilinear identities are reused from
[IsometryWeights](IsometryWeights.md). The quadratic value is homogeneous of degree two under central multiplication.
If the square of a weight takes a value different from one, preservation forces
its entire weight space to be singular. For two such weights whose product also
takes a value different from one, polarization forces the sum of their spaces
to be totally singular. If the weights are distinct and both spaces are nonzero,
disjointness and the submodule dimension formula give a singular subspace of
`D`-dimension at least two, hence quadratic Witt index at least two.

The statements retain the precise scalar-value nontriviality conditions. No
torus decomposition or group-rank conclusion is assumed or asserted in this
linear-algebra prerequisite, and no characteristic restriction is used.

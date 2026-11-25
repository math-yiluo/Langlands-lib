# Inverse-transpose pullback on actual automorphic forms

This internal construction for the proof of
`CuspidalTransposeInverseContragredientStatement` combines the actual finite-smooth
pullback with the concrete standard compact subgroup. It works over an
arbitrary-universe number field and at every natural matrix size.

The matrix transpose is a continuous real-linear map on the finite-dimensional
archimedean matrix algebra. Its operator norm bounds the norm of a transposed
matrix. Since inverse transpose exchanges the matrix and inverse matrix, the
matrix/inverse height after pullback is bounded by its original height times
the maximum of one and that operator norm. The polynomial exponent is
unchanged and the growth constant is multiplied by the corresponding power
of this bound. Applying this argument to the reindexed finite slice proves
preservation of actual adelic polynomial growth. The involution gives reflection.

The complete orbit under the standard infinite compact subgroup is transported
to the linear image of the original orbit under `continuousTranspose`. The
proof compares generating ranges and reindexes the compact subgroup by the
proved involution `compactTranspose`. Restricting the linear equivalence to
these spans proves preservation and reflection of the single common compact
finiteness condition on the actual adelic function.

Together with finite level and simultaneous center finiteness preservation,
these two results prove preservation and reflection of all four conditions
in `IsAutomorphicForm`. Restriction to their actual subspace defines
`AutomorphicForms.transpose`, a complex-linear involution with the stated
evaluation and finite-translation covariance.

This result does not establish preservation of cuspidality, an operator
realization, or the contragredient identification.
`CuspidalTransposeInverseContragredientStatement` is proved as
`cuspidalTransposeInverseContragredient` in
`Global/RankinSelberg/CuspidalTransposeInverseContragredientProof`.

# Linearized norm-one equations for the split odd quadratic form

The module constructs the vector subspace of matrices `Y` for which
`YQ + QYᵀ` is alternating and `trace Y = 0`. These are the linearized
quadratic and determinant-one equations at the identity. The construction
and block calculations work over every field and retain characteristic two.

The hyperbolic block satisfies the usual even orthogonal infinitesimal
condition. That condition pairs opposite diagonal entries with negatives,
so its trace vanishes without division by two. The total trace condition
therefore forces the axis diagonal to vanish. The off-axis polar equations
force the axis row to equal minus twice the paired axis column.

It follows that every matrix in this subspace is its embedded hyperbolic
block plus the sum of the signed short-family tangent matrices, with
coefficients from the axis column. These explicit identities are intended
for the tangent-surjectivity proof of smoothness. This module itself makes
no smoothness, connectedness or reductivity assertion, and does not yet
identify this subspace with the scheme Lie algebra.

This is internal linear algebra on the explicit split odd form and the
published even orthogonal infinitesimal equations, with no new literature
translation. The finite hyperbolic index lies in `Type`; the ground field
has arbitrary universe `u`.

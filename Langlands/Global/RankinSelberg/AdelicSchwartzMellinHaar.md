# Rank-one Mellin convergence for arbitrary idele Haar measures

This internal helper transports the rank-one full-idele convergence result of
`AdelicSchwartzMellin` from the normalized measure on actual adelic `GL_1`
points to any Haar measure on the actual idele group. It introduces no new
analytic estimate or assumption.

The determinant gives a continuous group isomorphism from the rank-one points
to ideles, with inverse given by the scalar matrix. Its single last-row entry
is the underlying adele of that determinant. The normalized idele measure is
a positive finite scalar multiple of Haar measure. Under a continuous group
isomorphism a Haar measure maps to a Haar measure, and Haar uniqueness compares
it to the chosen target measure by a positive finite scalar. Such a scalar
preserves finiteness of a nonnegative integral.

The resulting theorem proves convergence for continuous dominated rank-one row
functions and real exponent greater than `3`, for every idele Haar normalization.
The Schwartz–Bruhat corollary uses the published continuity and domination
properties, retaining their compactness hypothesis on the additive adelic
quotient.

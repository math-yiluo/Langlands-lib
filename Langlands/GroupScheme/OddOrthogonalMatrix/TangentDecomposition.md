# Actual factorization of odd identity tangent points

The signed short subgroup evaluated at an additive epsilon coordinate has
matrix `1+ε(c * shortVector a)`. The even block of a coefficient matrix in
`lieMatrices` defines an actual normalized even orthogonal point; its image
under `evenMap` has matrix `1+ε(evenEmbed(evenPart Y))`. The determinant
correction has no epsilon coefficient because the even infinitesimal trace
is zero. Both source points reduce to their actual identities.

Matrix multiplication of these dual-number points adds their coefficients.
The block decomposition from `LieMatrices` therefore proves that the
normalized odd tangent point factors as its even tangent image followed by
one signed short tangent image per signed coordinate, in the order of the
finite coordinate enumeration. Every actual Library identity tangent point
is the constructed point associated to its unique coefficient matrix.

These are actual point factorizations over the dual numbers, without a
smoothness assumption on the odd group. They are intended for surjectivity
on tangent vectors of the corresponding ordered product morphism. This
module does not assert that morphism is smooth or that the odd group is
connected or reductive.

This is an internal square-zero calculation using the previously constructed
actual affine subgroup formulas, with no new literature translation. The
field has arbitrary universe `u`; the finite hyperbolic index lies in `Type`.

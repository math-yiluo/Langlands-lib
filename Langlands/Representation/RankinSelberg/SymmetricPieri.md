# Elementary Pieri identity

Author: Worker 1767.

This internal algebraic helper adds one to the coordinates in a chosen subset.
For every coordinatewise nonnegative integral weight in rank `n + 1`, the
Jacobi–Trudi polynomial times the elementary symmetric polynomial of degree `k`
is the sum of the Jacobi–Trudi polynomials of the weights obtained by raising
exactly `k` coordinates.

The proof uses the cross-multiplied bialternant identity. Raising an exponent in
one alternant row multiplies each entry in column `j` of that row by `X j`.
The determinant subset expansion therefore computes the sum of the raised
alternants as the original alternant times the elementary symmetric polynomial.
The base alternant is a nonzero polynomial over a coefficient domain and is
cancelled in the polynomial ring. There is no cancellation after specializing
the variables.

The identity retains every subset term; dominance and the vanishing of
nondominant raised terms are separate obligations. It is proved over every
commutative coefficient domain and asserts no Whittaker model identification
or integral evaluation.

# Integral last-row support from polynomial degree coefficients

Author: Worker 952.

This internal reduction uses the published Iwasawa cell expansion in
`SphericalSeparation` and the algebraic coefficient obstruction in
`SchurPolynomialSupport`. `HasPolynomialCorankOneDegreeCoefficients` means that
all degree coefficients of the actual corank-one model integral are images of
ordinary multivariate polynomials in the torus coordinate algebra.

At a dominant torus point with negative last exponent, isolate the corresponding
Schur coefficient in the finite degree-cell expansion. Polynomiality forces that
coefficient to vanish. Positive cell mass and nonzero determinant and half-modulus
factors imply vanishing of the original Whittaker value.

For an arbitrary matrix, Iwasawa decomposition writes it as an upper unipotent
matrix times the uniformizer torus times an integral matrix. Restriction invariance
and Whittaker equivariance show that a nonzero value remains nonzero at the torus
point. The published non-dominant vanishing and the dominant negative-last-exponent
vanishing just proved imply a nonnegative last exponent. The last row of the
original matrix equals that uniformizer power times the last row of the integral
factor, so every entry is integral. This includes rank one for the smaller matrix.

This is a conditional reduction for arbitrary nonarchimedean local fields. It
assumes smoothness and right integral invariance of the restriction, and retains
polynomiality as its explicit input. It does not itself establish polynomiality
from the essential-vector identity, essential-vector existence or the conductor
theorem. The finite-cell formula and coefficient argument are internal derivations
from the named Library modules; no independent claim from the original literature
is needed.

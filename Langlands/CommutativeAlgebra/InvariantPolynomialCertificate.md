# Polynomial certificates for the unit ideal in a subring

This is an internal algebraic supporting construction for the
homogeneous-quotient affineness argument. It assumes no group,
reductivity, characteristic or geometric property.

`linearFamilyPolynomial f F` substitutes the linear form
`sum_i X_i * f_i,j` into each variable of a polynomial F over a commutative
ground ring. The index of families is finite; the variable index of F is
arbitrary. Its evaluation at s is F evaluated at the corresponding linear
combinations of the families. The construction commutes with algebra maps
on coefficients, and its constant coefficient is the scalar extension of
the constant coefficient of F.

`exists_map_subring` lifts a polynomial whose coefficients belong to a subring
to a polynomial over that subring. `span_eq_top_of_polynomial_certificate`
uses this lift: if the constant coefficient is zero and evaluation at
elements s_i of the subring is one, those elements generate the unit ideal
in the subring itself. The proof evaluates the lifted polynomial modulo
their generated ideal. Every variable becomes zero, so the result is zero
by the constant-coefficient hypothesis, whereas the given evaluation is one.

The construction and lemmas are derived directly from multivariate polynomial
evaluation, coefficient-map range and ideal quotient operations in Mathlib.
They do not yet produce an invariant polynomial certificate or prove the
affineness of any scheme.

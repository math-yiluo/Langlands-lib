# Monomial minor coefficients

Author: Worker 1767.

This internal helper defines the coefficient matrix and monomial matrix for a
chosen tuple of natural exponents. In a minor of the finite rectangular series
matrix, each column contributes exactly its fixed formal parameter power.
The other minor is constant. Thus their determinant product contributes only
in the degree equal to the sum of the chosen exponents, with coefficient the
product of the two corresponding coefficient-ring determinants.

Applying this calculation to the finite Cauchy–Binet expansion gives the exact
finite coefficient formula. Simultaneously permuting the selected columns of
the first minor and rows of the second preserves the determinant product, by
matrix multiplication. All identities hold over every commutative ring and
make no analytic assertion.

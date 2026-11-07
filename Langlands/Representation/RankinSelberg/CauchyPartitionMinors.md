# Partitions and Cauchy minors

Author: Worker 1767.

This internal helper identifies strictly increasing natural exponent tuples
with nonnegative antitone integral weights: reverse the tuple and subtract
the staircase, or add the staircase and reverse in the other direction.
It proves both inverse identities, nonnegativity and monotonicity, and the
relation between total exponent sum and partition size.

For coefficients of an arbitrary formal series, reversing the columns of
the coefficient minor and transposing gives its Jacobi–Trudi matrix.
Reversing the rows of the monomial minor gives the corresponding weight
alternant. Simultaneous reordering preserves the product of the determinants,
so each Cauchy–Binet minor pair is precisely the Jacobi–Trudi determinant times
that weight alternant. The matrix identities themselves hold for every natural
exponent tuple; strict increase supplies the nonnegative partition interpretation.
All results are internal finite algebra and order consequences, with no analytic
or representation-theoretic claim.

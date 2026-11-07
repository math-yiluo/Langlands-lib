# Finite power series minor expansion

Author: Worker 1767.

This internal helper extends a formal series coefficient by zero to negative
integer degrees. It constructs the reversed Vandermonde alternant whose
column at `y j` is multiplied by the series rescaled at that variable. Its
determinant factors into the base alternant, the fixed formal parameter power,
and the product of those rescaled generating series.

Finite product coefficients and then determinant coefficients depend only on
entry coefficients through the chosen degree. A finite rectangular monomial
coefficient matrix times a constant power matrix has the same entry coefficients
through its truncation limit as the generating-series matrix. Applying the
finite Cauchy–Binet identity therefore gives an exact finite minor sum for
each determinant coefficient. All identities are formal over a commutative
coefficient ring; no convergence or Whittaker claim is asserted.

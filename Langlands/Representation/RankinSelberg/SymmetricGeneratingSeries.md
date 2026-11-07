# Generating series for symmetric polynomials

Author: Worker 1767.

This internal helper works with the published `MvPolynomial.hsymm`, which sums
monomials indexed by multisets of fixed cardinality. The coefficient of degree
`k` in the product of geometric series, one for each variable, is `hsymm k`.
The proof uses the equivalence between multisets of size `k` and natural-valued
finitely supported functions of total mass `k`. The geometric series factors
then give `completeSeries * ∏ i (1 - X_i t) = 1`.

These are derived algebraic identities used in the planned determinant proof
of the Whittaker formula. They do not yet identify representation-theoretic
Whittaker values or evaluate the Rankin–Selberg integral.

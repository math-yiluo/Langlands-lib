# Compact factorization for an idempotent matrix parabolic

Let \(D\) be a Hausdorff topological division ring with a real-valued
multiplicative absolute value. Suppose its closed unit ball \(O\) is a
compact open subring. For an idempotent \(e\) of \(M_n(D)\) put
\[
 P_e=\{p\in M_n(D)^\times:(1-e)pe=0\}.
\]
`divisionMatrixParabolicIwasawa` gives a compact open subgroup \(K\)
with \(M_n(D)^\times=P_e K\).

Right multiplication by \(e\) is an idempotent on the left \(D\)-module
of rows. The proof chooses bases of its image and kernel and identifies
their direct sum with the row space. In the resulting coordinates,
the idempotent is diagonal with initial ones followed by zeros. An
upper triangular matrix belongs to the parabolic of this diagonal
idempotent. `divisionMatrixIwasawa` gives a right integral factor
making each matrix upper triangular in these coordinates.

The subgroup of matrix units with forward and inverse entries in \(O\)
is open by continuity of the two inverse coordinates. It is compact
because the inverse-pair equations define a closed subset of the product
of two compact matrix sets. Pulling this subgroup back under the basis
conjugation gives \(K\) for the original idempotent. The resulting formula
uses \(P_e K\), with the inverse of the column-reduction factor on the right.

This gives the division-matrix case of the compact Iwasawa input used by
Harish-Chandra in *Admissible invariant distributions on reductive
\(p\)-adic groups*, §1.2, printed p. 7, after inversion of the product
order used there.

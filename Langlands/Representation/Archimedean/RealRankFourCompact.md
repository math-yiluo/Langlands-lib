# Compact polynomial for two equal-weight real induction blocks

The two columns of the matrix with rows `(1,0)`, `(-i,0)`, `(0,1)`, and
`(0,-i)` span the `i/2` eigenspace of the third left quaternion matrix.
For the compact argument, take the minor in these two columns after combining
rows zero and one, and rows two and three, using independently chosen signs
of `i`. The sum of the \(m\)-th powers of these four minors, for
\(m=|\mathrm{weight}|+1\), has the diagonal sign parity of the two inducing
blocks and only the modes \(\pm m\) under each block rotation.
`RealKTypeTransport.mem_realStandardModule_of_unitaryCompact` puts its
principal-series extension in the compact-finite standard module. At the
identity exactly one minor contributes, giving the value \(4^m\).

Differentiating on the compact group along right multiplication by a matrix
exponential gives the tangent of the minor polynomial. For a tangent of the
form \(YD\), each minor of the two-column matrix \(Y\) has derivative equal
to that minor times \(\operatorname{tr}(D)\). The three right quaternion
matrices restrict to traceless matrices on the column plane, so their
actions annihilate the vector. The third left quaternion matrix restricts
to \(i/2\) times the identity and acts on the vector by \(mi\). The raising
matrix annihilates the column plane and gives zero derivative. The
principal-series restriction to the compact group is injective, so these
identities hold in the standard module.

This polynomial is an internal construction for the necessity argument for
opposite real twists of the same discrete block. The range and reducibility
endpoint are in Badulescu and Renard (2010), Theorem 8.2, p. 1131 (PDF p. 18),
and Proposition 9.4, p. 1133 (PDF p. 20).

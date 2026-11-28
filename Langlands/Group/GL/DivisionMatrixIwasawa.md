# Upper triangular factorization over a division ring

Let \(D\) be a division ring with a real-valued multiplicative absolute
value \(v\). Suppose its closed unit ball is the subring \(O\).
`divisionMatrixIwasawa` proves that for every invertible \(n\times n\)
matrix \(g\), there is a matrix unit \(k\) whose entries and inverse
entries lie in \(O\) such that \(gk\) is upper triangular.

The proof inducts on the matrix size. The last row contains a nonzero
entry since \(g\) has an inverse. An integral permutation matrix moves
an entry of maximal absolute value to the last column. Write \(a\) for
this nonzero last entry and \(b_j\) for the other last-row entries.
Right multiplication by \(1-N\), with \(N\) supported on the other
positions of the last row and \(N_{nj}=a^{-1}b_j\), clears those entries.
Each \(a^{-1}b_j\) lies in \(O\) by maximality, and \(N^2=0\) makes
\(1+N\) the integral inverse.

The cleared last row and its nonzero diagonal entry imply that the
inverse has zeros in the same lower-left block. Thus the upper-left
blocks of the matrix and its inverse are inverse to each other. Apply
the smaller-rank result there and extend its integral unit by the
identity on the last coordinate. This preserves the cleared last row.

Harish-Chandra uses a compact Iwasawa factorization in *Admissible
invariant distributions on reductive \(p\)-adic groups*, §1.2, printed
p. 7. This column reduction gives the algebraic part of such a
factorization for matrix groups over local division algebras. The
integer ring of a local division algebra supplies \(O\). The elimination
adapts the field calculation in `Langlands.Representation.Whittaker.Iwasawa`
to left division in the pivot coefficient and uses two-sided inverses
to pass to smaller rank.

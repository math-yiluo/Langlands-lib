# Alternating identities for the theta factors

`alternating_thetaOf_inv` is the determinant cancellation used for Arthur's (17.9). It concerns an independent family \((v_i)_{i\in I}\) with nonempty finite index set and its Euclidean dual \((w_i)\) in the span. The Gram matrix \(G\) is positive definite. The Kronecker pairings for `gramDual` follow by multiplying its inverse Gram matrix by \(G\).

For a subset \(J\subseteq I\), take the mixed family of \(v_j\) on \(J\) and \(w_i\) on its complement. The two parts are orthogonal. Its coefficient matrix in the \(v\) basis has rows from the identity on \(J\) and rows from \(G^{-1}\) elsewhere. After multiplying by \(G\), this matrix is block upper triangular with blocks \(G_J\) and the identity. The determinant of the mixed Gram matrix times \(\det G\) is therefore \((\det G_J)^2\). Taking nonnegative square roots shows that the product of the two partial Gram volumes times the full Gram volume equals \(\det G_J\).

Write \(x_i=\mathrm{i}\Lambda(v_i)\) and \(y_i=\mathrm{i}\Lambda(w_i)\). These satisfy \(Gy=x\). If each evaluation is nonzero, the matrix \(\operatorname{diag}(x^{-1})G-\operatorname{diag}(y^{-1})\) kills the nonzero vector \(y\). Expand its zero determinant by multilinearity in the rows. The term for \(J\) is its principal Gram determinant times the inverse evaluations on \(J\) and its complement, with sign \((-1)^{|I|-|J|}\). Dividing by the full Gram volume gives the sum of products of the two inverse theta factors. The proof keeps the factors of the imaginary unit and the Euclidean Gram volumes of `thetaOf`.

This algebraic identity is derived from the factors in Arthur's (17.9). The exact source is recorded in [Arthur's product splitting formula](GMFamiliesSplittingProof.md).

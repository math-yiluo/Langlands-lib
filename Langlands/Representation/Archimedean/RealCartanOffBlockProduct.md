# Invariance of the normalized product across Cartan blocks

Conjugating each square block conjugates the off-block endomorphism by the corresponding
left and right changes of coordinates on rectangular matrices. Reindexing the square block
coordinates likewise conjugates the endomorphism by rectangular matrix reindexing. In both
cases the determinants of the endomorphism and the identity minus the endomorphism are
unchanged, so the normalized off-block determinant is unchanged.

`normalizedOffBlockProduct` uses the reversal-invariant factor on the symmetric square of the
block labels, restricted to pairs with distinct entries. Relabelling the blocks transports
these unordered pairs bijectively and preserves each factor. A size-preserving assignment
can also reindex and conjugate each destination block independently. In a linear order the
product equals both the increasing-pair and the decreasing-pair product. The proof sorts each
unordered pair and uses pair symmetry to switch the order.

If the two Gram products of each block are scalar matrices and these scalars distinguish
the labels, each off-block determinant of the identity minus the action is nonzero.
A fixed rectangular matrix `X` would satisfy `g X = X h`. The trace of the transpose
times the matrix on the two sides is the trace of `Xᵀ X` multiplied by the two distinct
Gram scalars. Thus `X` is zero. The normalized product is nonzero because each of its
factors has a nonzero numerator and denominator. These are internal finite determinant
identities for the regular real Cartan normalization.

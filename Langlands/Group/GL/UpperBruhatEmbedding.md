# Ordered coordinate insertion for upper triangular matrices

Authors: Worker 308.

This internal construction supports the induction in the general-field upper
Bruhat factorization. It is not a claim of factorization existence.

`optionMatrix` adds one isolated diagonal entry equal to one. `optionGL` adds the
same coordinate to an actual invertible matrix and its inverse. `insert p` moves
that new coordinate to `p : Fin (n+1)` and places the original coordinates in the
increasing complement, enumerated by `p.succAbove`. It is a group homomorphism.
Its entry formulas and `insert_upper` establish that upper triangularity is
preserved, including for the empty original index set.

`extendPerm p w` sends `p` to the last row and `p.succAbove j` to `(w j).castSucc`.
Thus it uses exactly the column-to-row convention of the published permutation
matrices. All constructions work over any commutative ring and in every rank.

The proofs use an explicit optional-coordinate matrix, finite sums over `Option`,
and reindexing by Mathlib's `finSuccEquiv'`. Strict monotonicity of `succAbove`
proves the triangularity assertion. These are derived internal constructions
from the project's pivot-induction design; no external source theorem is claimed.

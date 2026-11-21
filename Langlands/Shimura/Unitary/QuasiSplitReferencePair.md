# The quasi-split unitary reference pair

The split central simple algebra over the given CM field is the actual
matrix algebra of size `n`. Its second-kind involution is the adjoint of
the antidiagonal Gram matrix for entrywise CM conjugation followed by
transpose. The matrix swaps each pair of opposite basis lines and fixes
the middle line in odd rank, giving one hyperbolic plane per pair.
The algebra has dimension `n ^ 2` over its center.

This is a derived realization of the quasi-split reference group
\(U_0\) in Clozel 1991, §2.1. The conjugate transpose displayed on
printed p. 102 is the identity-Gram adjoint and gives a definite form
at real places. The antidiagonal Gram matrix gives the maximal Witt
index, and in even rank \(n=2m\) its real signature is \((m,m)\), as
used in the proof of Lemma 2.2 on printed pp. 104–105. The construction
uses the maximal-Witt adjoint already defined in `FiniteModels`.

At every finite place, the entrywise matrix tensor equivalence sends
the base-changed reference involution to the maximal-Witt adjoint over
the actual completed quadratic center. The proof evaluates the
involution at entries, where each antidiagonal multiplication reverses
one index. On the image of the center, the same equivalence sends a
pure tensor to its scalar matrix. This verifies both conditions of the
Library's `IsQuasiSplitAt` and supplies the trivial local classes for
the arithmetic realization problem.

# Smoothing eigenspace traces along a Hilbert sum

Let \(H\) be the Hilbert sum of closed subspaces \(W_i\), and let \(T\)
be a symmetric trace-class operator preserving each \(W_i\).
`SmoothingEigenspaceHilbertSumStatement` expresses the trace of a bounded
operator \(A\) compressed to the eigenspace of \(T\) at \(z\ne 0\) as a
finite sum. Its summands are the traces of the compressions of \(A\) to
the \(z\)-eigenspaces of \(T|_{W_i}\). The finite index set depends on
the eigenspace and the Hilbert sum. It works for every \(A\).

The proof first shows that \(T\) commutes with the orthogonal projection
to each \(W_i\). Symmetry and preservation of \(W_i\) make
\(T(x-P_i x)\) orthogonal to \(W_i\), where \(P_i\) is its projection.
The projections of a vector of eigenvalue \(z\) therefore retain that
eigenvalue and lie in the respective intersections. These intersections
form a Hilbert sum of the full eigenspace. Indeed, a vector perpendicular
to all of them has zero projection to every \(W_i\) and hence is zero.

The eigenspace at a nonzero eigenvalue is finite-dimensional by compactness.
Choosing one nonzero vector from each nonzero intersection yields an
orthogonal and thus linearly independent family. This proves that the
intersections with nonzero dimension form a finite set. The proof applies
`hilbertSum_trace_hasSum` on the eigenspace and drops the zero terms.
For each retained summand, the isometry from the eigenspace of \(T|_{W_i}\)
to the intersection identifies the diagonal entries of the compressed
operators in corresponding orthonormal bases.

`summandCompression` is the orthogonal compression of a bounded operator.
It preserves symmetry. If \(T\) preserves \(W_i\), the compression of
\(AT^k\) to \(W_i\) equals the compression of \(A\) followed on the right
by the \(k\)-th power of the compression of \(T\). This identity uses
only the preservation of \(W_i\) by \(T\).

The finite-sum result is a derived operator step for the local
trace-factor comparison on the cuspidal spectral side of Arthur–Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula* (1989), Chapter 1, §4, printed pp. 43–45.

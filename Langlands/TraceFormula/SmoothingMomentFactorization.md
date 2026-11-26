# Local trace factors on nonzero smoothing eigenspaces

Let \(T\) be a symmetric trace-class operator on a complex Hilbert space.
Let \(A_i\) be a family of bounded operators. Suppose
\(\operatorname{tr}(A_i T^{k+1})=L(i)C(k)\) for every test index \(i\) and
every \(k\geq 0\). `SmoothingMomentFactorizationStatement` shows that on
each nonzero eigenspace of \(T\) the traces of the compressed \(A_i\) are
\(L(i)c\) for one scalar \(c\) depending on the eigenvalue.

To transfer a vanishing relation of the power traces to an eigenspace,
the proof applies `compactOperatorTraceReplacement` with the
replacement \(P_z A\), where \(P_z\) projects orthogonally to the
eigenspace of eigenvalue \(z\). The eigenspaces of a symmetric operator
are mutually orthogonal. The compression of \(P_z A\) on the eigenspace
at \(z\) equals the compression of \(A\). Its compression on every other
eigenspace is zero. The replacement theorem gives
\(\operatorname{tr}(P_z A T)=0\). When \(z\ne 0\), the eigenspace is
finite-dimensional. Rectangular cyclicity through this space identifies
the last trace with \(z\) times the compressed trace of \(A\).

If some \(L(i_0)\) is nonzero, apply this argument to
\(A_i-(L(i)/L(i_0))A_{i_0}\) and use linearity of the finite-dimensional
compression trace. If every \(L(i)\) is zero, apply the argument to each
\(A_i\) and take \(c=0\).

This operator identity is a derived step for using local character
factors in a spectral comparison. Arthur–Clozel separate the local
factors of the cuspidal spectral side in *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula* (1989), Chapter 1, §4,
formulas (4.6)–(4.7), printed pp. 43–44.

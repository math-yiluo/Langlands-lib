# Finite local trace expansions on smoothing eigenspaces

`FiniteSmoothingTraceExpansionStatement` starts with a complex Hilbert
space \(H\), an orthogonal Hilbert decomposition \(H=\widehat\bigoplus_j W_j\),
and a symmetric trace-class operator \(T\) preserving each \(W_j\).
Suppose the compression of each \(A_i T^{k+1}\) to \(W_j\) has trace
\(L_j(i)C_j(k)\), for a bounded test family \(A_i\) and all \(k\geq 0\).
For every nonzero smoothing eigenvalue \(z\), the trace of \(A_i\) on
the \(z\)-eigenspace, compressed by its orthogonal projection, has the form
\[
  \operatorname{tr}\bigl(P_z A_i|_{\ker(T-z)}\bigr)
    = \sum_{j\in D_z} c_{z,j} L_j(i).
\]
The finite set \(D_z\) and coefficients \(c_{z,j}\) are common to all tests.
The formula also holds for a nonzero \(z\) with zero eigenspace.

`smoothingEigenspaceHilbertSum` gives the finite sum of the summand
compressions, uniformly for every bounded \(A_i\). On each summand,
`summandCompression_mul_pow` puts the operator powers entirely
on that summand. The compression of \(T\) is symmetric and trace class,
so `smoothingMomentFactorization` turns the given power traces into
the desired factors on the nonzero eigenspace. Substituting those factors
into the finite sum proves the formula.

In the trace comparison, \(L_j\) is the local distribution of an ordinary
or twisted cuspidal summand. The finite sum makes character separation
applicable on each eigenspace. Arthur–Clozel, *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula* (1989), Ch. 1, §4,
formulas (4.6)–(4.7) and Lemma 4.10, printed pp. 43–45 (PDF pp. 57–59),
uses finite sums after separating the archimedean components. Here the
finite sums use the nonzero eigenspaces of a trace-class smoothing operator.

Source ID `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.

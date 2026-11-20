# A compact kernel formula for the real standard averaging trace

The compact restriction of a compact-finite vector is polynomial in the
entries of \(O(n)\). Let \(P\) be a linear left inverse of this restriction
with values in the actual compact-finite real standard module. For each
compact polynomial cutoff \(\varphi\) and real invertible \(g\), the
averaging trace is the integral over \(y \in O(n)\) of
\[
  \bigl(P[x \mapsto \varphi(x^{-1}y)]\bigr)(y g).
\]
The result uses the same Haar measure as `averageTrace`. It applies to
any supplied \(P\) with the left inverse property.

The kernel belongs to the Library's span of separated products of
polynomial and continuous functions. The proof writes it as a finite sum
\(\sum_i a_i(x)b_i(y)\). After the compact change of variables and
application of \(P\), the averaging operator is the sum of the vectors
\(P(a_i)\) times the functionals \(f \mapsto \int b_i(y)f(yg)\,dy\).
Its range lies in the finite-dimensional span of these vectors. Trace
cyclicity identifies the range trace with the trace on this larger span.
The rank-one trace formula and finite sum integration give the stated
integral.

This internal formula uses the separated polynomial convolution kernel
of `OrthogonalFinitePolynomial` and the range trace of
`RealStandardCompactTrace`. For a Cartan character calculation one can
instantiate the left inverse by extending the compact sign and
rotation Fourier projections.

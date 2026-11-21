# The canonical complex Jacquet continuation is a Whittaker intertwiner

`ComplexJacquetCanonicalIntertwinerStatement` identifies canonical evaluation
at every radial parameter as a Whittaker intertwiner of the compact-finite
complex standard module. The evaluation uses Fourier parameter \(a\) and has
left Whittaker character for \(-a\). The additive Haar measure is arbitrary.

The integrated Lie identity gives differentiability in the open matrix chart.
The candidate Fréchet derivative evaluates the standard Lie derivative in
right direction \(g^{-1}Y\) at the point \(g\), for a matrix increment \(Y\).
It is expressed as a finite sum over a real matrix basis and is continuous in
\(g\). For a nearby invertible matrix, the segment from \(g\) stays in an open
ball of invertible matrices. The integrated identity expresses the increment
of the coefficient as the integral of the candidate derivative along the
segment. Its continuity bounds the first-order remainder by an arbitrarily
small constant times the increment norm. Induction on the order of
smoothness uses the same derivative formula for all inducing vectors and
smoothness of matrix inversion on the invertible locus. Evaluating the
Fréchet derivative on \(gX\) gives right Lie equivariance.

For moderate growth, the diagonal entries of the Iwasawa triangular factor
and its inverse are the exponentials of the Iwasawa coordinates and their
negatives. Both entry norms are bounded by a constant times the matrix
height, using the height bound on the compact factor and submultiplicativity.
The canonical simple-root estimate at decay order zero is therefore bounded
by a power of the height. Left Whittaker covariance and right unitary
covariance are those of canonical evaluation. These are precisely the
clauses of `IsComplexWhittakerIntertwiner`.

This internal result supplies the exact Library model membership of the
continued coefficients in Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), §7.2 and Proposition 7.2 on printed p. 48. The proof implements
the differential step by continuing the integrated chamber identity.

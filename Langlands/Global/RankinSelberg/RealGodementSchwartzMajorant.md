# An integrable majorant for general real Godement tests

`RealGodementSchwartzMajorantStatement` bounds the norm of the lower-group kernel for an arbitrary rectangular Schwartz function. For a smooth lower position vector and the stated inequalities on the real part of the leading exponent, one Haar-integrable majorant works uniformly for all upper translating matrices in a fixed compact set.

The proof writes the inverse of each lower matrix in Iwasawa form. The absolute determinant is the product of the inverse absolute diagonal entries. Each of those entries is bounded by a constant times one plus the norm of the lower matrix, because the inverse triangular factor is the lower matrix multiplied on the left by an orthogonal matrix. After accounting for the determinant density in Haar measure, all remaining diagonal powers have nonnegative exponents. Their product has polynomial growth in the matrix norm. On the compact set of translating matrices, the trailing rows have a continuous choice of right inverse obtained from the inverse matrix. This compares the lower matrix norm to the rectangular argument of the Schwartz function with a common constant. Its rapid decay absorbs the polynomial growth and supplies the integrable matrix-space decay.

This is a derived estimate for the convergence of the Godement sections in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.1, equation (7.1), pp. 43–45, and their use in the open-cell calculation at §7.2, pp. 47–48. The Lean estimate specifies a right half-plane through the inequalities on the inducing exponents and uses the actual real matrix Haar density.

`exists_uniform_schwartz_decay` gives the uniform polynomial decay bound
for each iterated Fréchet derivative of the test. The majorant in the
statement uses order zero. `exists_integrable_matrixDecay` gives the Haar
integrability bound after multiplication by the forward determinant density.

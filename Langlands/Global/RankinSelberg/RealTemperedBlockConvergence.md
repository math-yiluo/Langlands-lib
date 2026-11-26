# Sharp convergence of the reflected real rectangular integral

`realTemperedBlockConvergence` proves absolute convergence of the
real unequal-rank dual kernel and holomorphy of its iterated integral on
\(\operatorname{Re}s>0\). It assumes that both regular Whittaker
functions satisfy `HasTemperedGauge` for their respective opposite
additive characters. The quotient measure is the supplied compatible
measure, and the measure on the rectangular entries is self-dual for the
supplied additive parameter.

On the rectangular Iwasawa chart, each log diagonal entry differs from
the corresponding entry of the zero-padded smaller log diagonal by at
most \(\tfrac12\log(1+\lVert X\rVert_F^2)\). This follows separately
for the first block, the middle block and the final entry from the
published Iwasawa bounds. Hence the modulus contributes the same
toral factor as for a padded diagonal, with a polynomial error in
\(1+\lVert X\rVert_F^2\).

The reflected Whittaker functions satisfy the same estimates because
the dual transformation and the orthogonal right translation preserve
the gauge. The positive simple-root decay at the rectangular point
absorbs the polynomial error and gives an integrable product of
\((1+X_{ij}^2)^{-1}\) over the entries. The padded modulus cancels the
determinant shift and the two remaining half-moduli cancel the
quotient density. For a real spectral part \(\tau>0\), choosing the two
residual growth exponents to be \(\tau/4\) gives toral domination by
\(\exp(-(\tau/2)\sum_i |y_i|)\) against Lebesgue measure. Differentiation
under the integral applies to the product integral. Absolute
convergence identifies it with the iterated integral on the half-plane.

The statement formalizes the remaining rectangular integration in the
tempered convergence argument, given the Whittaker estimate. [Jacquet, *Archimedean Rankin–Selberg integrals*, Lemma 5.3](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

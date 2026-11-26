# Sharp ordinary real convergence from tempered Whittaker bounds

For a function \(W\) on \(\mathrm{GL}_n(\mathbb R)\), `HasTemperedGauge`
requires the following estimate for all \(\varepsilon>0\) and all
nonnegative integers \(J\), with a constant depending on both:
\[
 |W(a(y)k)|\ \leq\ C\exp\!\left(\frac12 M_n(y)
         +\varepsilon\sum_i |y_i|-J\sum_{i<n-1}\max(y_i-y_{i+1},0)\right).
\]
Here \(a(y)=\operatorname{diag}(e^{y_i})\), \(k\) is orthogonal, and
\(M_n\) is `torusModularLog`. `HasTemperedDerivativeBound` requires the
estimate with \(J=0\) for each right-derivative word. With the
character-equivariance of every right derivative, the simple-root
argument of `exists_weighted_bound_list_family` gives `HasTemperedGauge`.
The gauge passes to the dual function because reversal and negation of
the logarithmic diagonal preserve \(M_n\), the absolute-value sum and
the positive simple-root sum.

`realTemperedOrdinaryConvergence` assumes the gauge for both regular
Whittaker functions with opposite characters. It proves absolute
convergence and holomorphy on \(\operatorname{Re}s>0\) for the ordinary
unequal-rank integral and for both the original and Fourier-reflected
equal-rank integrals. The quotient measures are the supplied compatible
measures.

In equal rank the two half-moduli cancel the inverse modulus from the
toral density. Schwartz decay supplies arbitrary decay as the last
diagonal coordinate tends to infinity. In unequal rank the padded
modulus also contributes \((n-m)\sum_i y_i/2\) to the exponent,
cancelled by the determinant shift. The extra simple root of the padded
diagonal gives decay in the positive part of the last coordinate.
For each spectral real part \(\tau>0\), the arbitrary positive growth
error can be chosen small enough that the density-weighted integrand
is dominated by \(C\exp(-c\sum_i|y_i|)\) with \(c>0\). The integrable
majorants at nearby real parts justify complex differentiation under
the integral.

This formalizes the ordinary toral integrations of Jacquet's tempered
convergence argument from a supplied estimate of the Whittaker
functions. The weaker exponential error used here accommodates the
polynomial factor in the logarithmic coordinate of Proposition 3.4.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Propositions 3.4 and 3.5 and Lemmas 5.3 and 5.4](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

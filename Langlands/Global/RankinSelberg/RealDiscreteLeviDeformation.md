# Dominant spectral deformations for real discrete blocks

`blockStart` labels each position by the first position of its nonzero-weight
induced pair or by its own index for a singleton. It treats the two
positions of a weight-zero block as singletons. The labels increase weakly.
Two successive positions have equal labels exactly when they form a
nonzero-weight induced pair.

`exponentPath` starts at the descending position exponents \(z_i\) and
subtracts \(t\,\mathrm{blockStart}(i)\) from each exponent. This path is
holomorphic. `exponentPath_pair_gap` preserves the positive exponent gap
\(\lvert m\rvert\) in a nonzero-weight pair of weight \(m\).
`exponentPath_mem_chamber` shows that every adjacent gap has positive real
part when \(\operatorname{Re}t\) is sufficiently large, uniformly in
\(\operatorname{Im}t\). Within a pair, the gap is fixed. At a class boundary,
the gap increases by at least \(\operatorname{Re}t\).

`RealLeviDeformationMajorantStatement` concerns any weakly increasing
natural-number labels \(c_i\). For an opposite radical matrix \(v(X)\) in
the lower entry chart, let \(y\) be its logarithmic Iwasawa diagonal. For
each \(\delta>0\), `realLeviDeformationMajorant` supplies a continuous
Lebesgue-integrable function of \(X\) bounding
\[
  \exp\!\left(\frac{\log\delta_B(y)}2-\tau\sum_i y_i c_i\right)
  \qquad(\tau\ge\delta).
\]
Here \(\log\delta_B(y)\) is `torusModularLog` evaluated at \(y\). The proof
identifies this expression with the norm of the spherical section with
position exponents \(-\tau c_i\) and applies `RealLeviTorus.norm_le_gram_fin`.
The resulting exponent on the Gram determinant at position \(i>0\) is
\((\tau(c_{i-1}-c_i)-1)/2\). Each Gram determinant is at least one, so
using \(\delta\) in place of \(\tau\) gives a common bound. The exponents
are at most \(-1/2\), with strict inequality at each change of label,
as required by `RealLeviChartIntegrable.gen`.

The labels and spectral shift are consequences of the position exponents
of the real standard module. The common majorant uses Gram-determinant
integrability for the opposite radical of the parabolic defined by those
labels.

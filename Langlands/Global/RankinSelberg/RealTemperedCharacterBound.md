# The tempered Whittaker bound for real character lists

`realTemperedWhittakerCharacterBound` proves `RealTemperedWhittakerCharacterBoundStatement`. For every rank-correct list of real characters and weight-zero induced blocks with purely imaginary exponents, every element \(W\) of the exact real Whittaker model satisfies
\[
 |W(a(y)k)|\leq C_{W,\epsilon}\exp\!\left(\tfrac12 M(y)+\epsilon\sum_j|y_j|\right)
 \quad(\epsilon>0).
\]
Here \(M\) is the logarithm of the upper-unipotent modulus at the positive diagonal \(a(y)\), and the estimate is uniform in \(y\) and the orthogonal matrix \(k\). The additive scale is any nonzero real unit.

For a character presentation, exact and uniform model equality and the canonical range theorem express \(W\) as a continued Jacquet coefficient of an orthogonal profile. Keep that profile fixed and perturb its exponents by \(z_j-tj\), where the \(z_j\) are imaginary. On each line \(\operatorname{Re}t=\delta>0\) the exponents are strictly dominant, so the coefficient equals the absolutely convergent open-cell integral. Move the positive diagonal past the upper unipotent and the long Weyl element. The change of variables contributes \(\exp(M(y))\), and the normalized inducing covariance contributes the reversed half-modulus \(\exp(-M(y)/2)\) and the inducing powers. The latter are bounded by \(\exp(r\delta\sum_j|y_j|)\), with \(r+1\) the rank. The additive phase has norm one. The remaining integrand is dominated in norm by a constant times the absolutely integrable spherical section with the same real exponents. The constant is the bound of the fixed profile on the compact group.

On the closed parameter disk of radius two, the continued Jacquet family has uniform polynomial height growth. On the diagonal this gives an exponential bound in \(\sum_j|y_j|\). Remove the half-modulus and apply `smallExponentialAtZero_of_rightBoundary` to obtain an arbitrarily small exponential loss at \(t=0\). The scalar bound for blocks of weight zero follows by ascending character expansion, which preserves imaginary exponents in this case and contains the original exact model.

This is the scalar consequence of the estimate in H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Proposition 3.4, author p. 21, restricted to these lists. The proof uses the open-cell formula of §7.2, author p. 47, and holomorphic interpolation of the canonical Jacquet family. [Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)

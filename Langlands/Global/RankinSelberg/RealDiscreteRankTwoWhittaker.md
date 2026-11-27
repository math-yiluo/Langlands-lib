# The real rank-two discrete block on the diagonal

The Gram polynomial of a single real discrete-series block is a
compact-finite standard vector. The nonzero weight makes its two
position exponents strictly dominant, so its open-cell Jacquet
coefficient belongs to the ordinary Whittaker model at scale \(1\).

The group argument on the diagonal is the matrix with rows
\((0,1)\) and \((a,x)\), where \(x\) is the upper unipotent
coordinate. Its upper-triangular and orthogonal decomposition has
positive diagonal entries \(|a|/\sqrt{a^2+x^2}\) and
\(\sqrt{a^2+x^2}\). The two summands of the compact Gram polynomial
select the sign of \(a\). Combining the angular power with the
triangular weights gives a reciprocal power of
\(|a|-i\,\operatorname{sgn}(a)x\).

The self-dual upper-entry measure at the open-cell parameter \(-1\)
is Lebesgue measure and the phase is \(e^{-2\pi i x}\). The scalar
Fourier formula therefore evaluates the transform at \(\operatorname{sgn}(a)\).
It vanishes for \(a<0\). For \(a>0\) the result is
\(C a^{\,u+(|m|+1)/2}e^{-2\pi a}\), where \(m\) is the block weight,
\(u\) is its exponent, and the explicit constant \(C\) is nonzero.

This provides a compact-finite vector with the positive-half-line
Whittaker behavior used for \(GL_2(\mathbb R)\) in H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), §12.4, pp. 90–91 of the
author-posted version. The proof uses the open-cell Gram vector and
scalar Fourier inversion in place of a smooth Schwartz model.

## The estimate for the exact model

`realDiscreteWhittakerBound` proves `RealDiscreteWhittakerBoundStatement`. For a single real induced block with nonzero weight and complex exponent \(u\), every coefficient in the exact model at any nonzero real additive scale satisfies
\[
  |W(\operatorname{diag}(e^{y_0},e^{y_1})k)|\leq
     C_W\exp\!\left((y_0-y_1)/2+\operatorname{Re}(u)(y_0+y_1)\right)
\]
for all real logarithmic diagonal entries and all \(k\in O(2)\). Thus the estimate at a purely imaginary twist is the upper Borel half-modulus, with no exponential loss.

The Jacquet cell \(w_2n(x)\) has determinant \(-1\). Its positive upper-triangular factor has determinant one, and its compact factor is the rotation by \(\arctan x\) followed by the long Weyl element. Evaluating an arbitrary compact-finite inducing vector on the cell gives the radial factor \((1+x^2)^{-(|m|+1)/2}\) times the resulting compact profile. Finite Fourier inversion on the rotation subgroup expands that profile into a sum with bounded degree. The block cutoff and the parity of the two inducing characters allow only indices \(\pm(|m|+1+2h)\). The Fourier coefficient of each permitted mode is bounded uniformly in the final orthogonal factor by the compact supremum of the inducing vector times the length of the integration interval. Applying `realDiscreteAngularFourierBound` mode by mode gives the bound by the absolute frequency to power \(|m|/2\).

Moving the positive diagonal through the open cell scales the unipotent coordinate by \(e^{y_0-y_1}\). The Jacobian, the inducing character on the reversed diagonal and the Fourier power bound combine to give the displayed estimate for the convergent Jacquet map. The self-dual measure contributes the constant \(|a|^{1/2}\). The lowest compact profile has nonzero Fourier value at the appropriate sign of the first diagonal for each nonzero additive scale. The ascending standard-module quotient pulls any two exact maps back to the character model. Proportionality there and surjectivity of the quotient show that the range of the nonzero convergent Jacquet map is the full exact model.

This gives the single nonzero-weight block case of the scalar estimate used in Jacquet's Proposition 3.4. The proof uses rotation Fourier inversion and the convergent Jacquet integral. [Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), Proposition 3.4, author-posted p. 21](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)

# The exponent difference in the real rank-two principal series

Worker 848.

`RealGLTwoPrincipalSeriesUnitaryBound.exponent_difference` proves
`RealGLTwoPrincipalSeriesUnitaryBoundStatement` by calculating with the
positive Hermitian form on the `O(2)`-finite standard module.

For a rotation \(r_\theta\) and every allowed integer mode \(j\), `exists_mode`
constructs a vector \(f_j\) whose value at \(r_\theta\) is \(e^{ij\theta}\).
The compact section is the product of a determinant power and powers of
\(k_{11}+ik_{10}\) and \(k_{11}-ik_{10}\), with matrix indices starting at
zero. Its sign under diagonal row changes gives the prescribed parities.
The mode \(j\) is allowed precisely when \(j\) is congruent to the sum of the
two parities modulo two. The values on rotations determine the vector since
each element of `O(2)` is a diagonal matrix times a rotation.

Write \(\nu=c-d\) for the complex exponent difference and let
\(H=\operatorname{diag}(1,-1)\). The Library's Fourier coefficient formula
`RealBlockDerivative.blockFourierCoefficient_rightDerivative` gives the
coefficients \((\nu+1+j)/2\) and \((\nu+1-j)/2\) of \(Hf_j\) in modes \(j+2\)
and \(j-2\). Invariance under rotation by \(\pi/4\) makes modes four steps
apart orthogonal. Taking the real part of the skewness relation on
\(f_j,f_{j+2}\) gives
\[
(\operatorname{Re}\nu+1+j) B+
(\operatorname{Re}\nu-1-j) A=0,
\qquad A=\langle f_j,f_j\rangle>0,\quad
B=\langle f_{j+2},f_{j+2}\rangle>0.
\]
For equal parities, \(j=0\) makes the sum strictly positive when
\(\operatorname{Re}\nu\ge 1\) and strictly negative when
\(\operatorname{Re}\nu\le -1\). For opposite parities, \(j=-1\) gives
\(\operatorname{Re}\nu(A+B)=0\).

The calculation uses the compact model and Fourier differentiation already
in the Library. The form invariance and skewness are the two conditions in
Knapp–Vogan (1995), display (0.5), printed p. 6 (PDF p. 28). Vogan (1986),
Definition 2.3 and Lemma 2.4(d)–(e), printed p. 452 (PDF p. 4), and
Proposition 2.5, printed p. 453 (PDF p. 5), give the normalization and
complementary interval for the common-character specialization.

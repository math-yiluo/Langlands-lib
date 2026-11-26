# Polynomial Fourier tests and transposed directional derivatives

`SchwartzPolynomialFourierTestStatement`, proved by `schwartzPolynomialFourierTest`,
uses the Mathlib Fourier kernels \(e^{-2\pi i\langle x,\xi\rangle}\) for the
forward transform and \(e^{+2\pi i\langle x,\xi\rangle}\) for the inverse.
Let \(a\) be a Schwartz test on a finite-dimensional real inner product space.
For a finite list of directions \(m_j\), the function

\[
x\longmapsto e^{-2\pi i\langle x,\xi\rangle}
  \left(\prod_j\langle x,m_j\rangle\right)(\mathcal F^{-1}a)(x)
\]

is integrable. Its integral is the iterated directional derivative of \(a\)
at \(\xi\), multiplied by \((-2\pi i)^{-n}\), with \(n\) the number of directions.
The empty list gives the Fourier inversion formula.

The proof iterates `SchwartzMap.fourierInv_lineDerivOp_eq` to express the
monomial times \(\mathcal F^{-1}a\) as a constant times the inverse Fourier
transform of the differentiated test. Multiplication by the unitary character
preserves the norm bound by an integrable Schwartz function. The integral is
then a forward Fourier evaluation, which cancels the inverse transform.

This is the monomial calculation for the test-side transpose of the
distributional derivative in P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107. See (7.10)–(7.11), p. 25,
Proposition 7.8, p. 33, and the passage to the limit in Lemma 7.11, p. 35.
The published PDF of `delorme-2023-spectral-theorem-langlands` has SHA-256
`9b2e82af72ac45c9745357d475153d43d29ec3e1ea68bf51980acf466110e2df`.
Delorme uses the positive kernel \(e^{it\cdot X}\), obtained by a rescaling of
these frequency coordinates. Moving the derivative onto the test gives the
negative scalar per derivative in both conventions.

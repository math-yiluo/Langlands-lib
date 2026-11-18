# The complex equal-rank kernels under a change of additive character

This module proves the integral comparisons used in the standard-character
reduction of Jacquet's equal-rank local equation. Write \(n=r+1\),
\(b=|a|\) with the usual absolute value, and
\(\beta=\omega_d(a)\omega_{d'}(a)\) for the two central characters.
The notation \(b^v\) for \(v\in\mathbb C\) means
\(\exp(v\log b)\). The exponent in the determinant kernel uses
the normalized absolute value \(|\det g|^2\). These conventions
are those of `ArchimedeanIntegrals.lean`.

Put \(t=\operatorname{diag}(a^r,\ldots,1)\). Let \(V,V'\) be the
left translates of \(W,W'\) by \(t^{-1}\), so their characters
are \(\psi_1,\psi_{-1}\). The quotient changes from
`ComplexLocalEqualQuotientChange.lean` give the following comparisons.

- At the primal point \(tg\), the normalized coefficient values are
  the original ones at \(g\), and the last row is unchanged.
  The determinant norm contributes \(b^{rn}\) because twice the sum
  of the diagonal exponents is \(rn\). Thus the original primal
  kernel is the standard-character kernel at \(tg\) multiplied by
  \(b^{-rns}\).
- At the dual point \(tg\,\operatorname{scalar}(a)\), the inverse
  transpose and the long Weyl matrix turn the inverse left translate
  into the scalar \(a^{-n}\) in the argument of each dual function.
  The scalar action gives the product factor \(\beta^{-n}\).
  The last row is \(a\) times the original last row, and the
  determinant norm contributes \(b^{n(r+2)}\).

For the Fourier comparison, the positive trace kernel transfers \(a\)
to the argument of the standard transform. Each self-dual measure
contributes a factor \(b\). The finite product measure and its integral
therefore give
\(\widehat\Phi_a(x)=b^n\widehat\Phi_1(ax)\).
Combining this formula with the dual point calculation, the original
dual kernel is the standard dual kernel at
\(tg\,\operatorname{scalar}(a)\) multiplied by
\(\beta^n b^{n-n(r+2)s}\).

The two shifts are measure-preserving homeomorphisms to the same
transported quotient measure. Multiplication by either scalar factor
preserves integrability in both directions, and the integral
change-of-variables formula gives the corresponding scalar identity
for each integral. The proof applies these formulas to the quotient
integrands with their original determinant powers and Fourier measures.

# Normalized Fourier evaluation in coroot coordinates

`CoordinatePolynomialFourierEvaluationStatement` computes the full spatial
integral of a reflected polynomial times the Fourier transform of a smooth
compactly supported test translated by a frequency \(\xi\). The spatial
measure is product Lebesgue measure. The spectral measure is product
Lebesgue measure times \((2\pi)^{-n}\) in dimension \(n\), which agrees with
`spectralMeasure` for coordinates indexed by `Fin n`.

This is the whole-space calculation for the surviving distribution in
the proof of Delorme's Lemma 7.11, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023) 109107. With
\(D_j=i^{-1}\partial/\partial z_j\) in the convention of (7.10)–(7.11),
Proposition 7.8 applies \(P(D)\) to the cone transform. In the whole-space
limit, moving these derivatives onto the test \(a\) gives
\([P(-D)a](\xi)\). The display of Lemma 7.11 on p. 35 writes \(P(D)\) on
the test.

Translation of the spectral variable gives the phase at \(\xi\). The
spatial change of variables \(x=-2\pi u\) gives Mathlib's inverse
Schwartz transform at \(u\), and its Jacobian cancels the spectral
normalization. A monomial with exponent vector \(k\) gives \(k_i\)
copies of the \(i\)th coordinate direction, indexed by the finite set of
pairs \((i,j)\) with \(j<k_i\). Applying
`fourierPolynomialPointEvaluation_spec` to those directions gives absolute
integrability and the value of each monomial integral. The powers of
\(2\pi\) in `coordinatePolynomialPointEvaluation` account for the same
spatial change of variables in the polynomial.

The differential evaluation depends only on the germ at \(\xi\). Applied
to the negative phase at a spatial point, it gives the original
polynomial at that point multiplied by the phase evaluated at \(\xi\).

# Polynomial point distributions and their Fourier phases

`fourierPolynomialPointEvaluation` evaluates an iterated real directional derivative at the given frequency. Each derivative is multiplied by \((-2\pi i)^{-1}\) in Mathlib's Fourier normalization. This defines the action on a test function from its germ at that frequency. For a Schwartz test, the action is the absolutely convergent whole-space Fourier integral of a monomial times a unitary phase and the inverse transform of the test.

The same differential evaluation acts on the negative Fourier phase at a prescribed spatial point. Its value is the spatial monomial times the value of that phase at the frequency. The proof writes the phase as the characteristic function of a Dirac measure at the scaled spatial point and uses the derivative formula for that function. The normalizing powers cancel. Locality follows from preservation of germs under iterated differentiation. The Schwartz identity follows from `schwartzPolynomialFourierTest`.

These are the point-mass and phase calculations underlying Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023), equations (7.10)–(7.12) and Lemma 7.11.

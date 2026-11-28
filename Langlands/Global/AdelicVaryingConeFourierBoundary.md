# Fourier boundary values with varying compact spectral coefficients

`RegularizedOrthantVaryingTestStatement` tests a regularized polynomial
orthant term against a spectral Schwartz function that varies with the
real displacement. Each displacement slope must be nonzero. If the
tests converge to the test at displacement zero in Schwartz topology,
the signed integrals converge to the integral of the limiting polynomial
Fourier test over the translated oriented orthant. The spectral measure
is `coordinateSpectralMeasure`, and the spatial measure is product
Lebesgue measure.

`regularizedOrthantTerm_integrable_integral` obtains absolute integrability
at each positive displacement and identifies the signed integral by Fubini.
It factors the Laplace kernel into a spatial weight times the unit-norm
coordinate phase. The weight contains the reflected polynomial and is
integrable on the orthant by `translatedOrthant_polynomialLaplace` at zero
imaginary part.

The spatial map taking a spectral test to its polynomial Fourier test is
continuous in Schwartz topology. The proof identifies the normalized
Fourier integral with a rescaled inverse Schwartz transform and multiplies
by the reflected polynomial, which has temperate growth. The images
therefore converge in spatial \(L^1\). With the damping written relative
to the translated vertex, it has absolute value at most one on the
oriented orthant. The integral of the varying part of the test is bounded
by the spatial \(L^1\) norm of its difference from the limiting test.
Dominated convergence removes the damping for the limiting test itself.
The scalar exponential from the vertex translation tends to one.

`regularizedOrthantFourierBoundary_compactFamily` obtains the Schwartz
convergence from joint smoothness and a common compact spectral support.
`translatedOrthant_compactTest_tendsto` then computes the translated
orthant integrals on a ray that grows in every coroot coordinate. For the
all-positive orientation the result is the normalized polynomial point
evaluation at the supplied frequency. If any displacement slope is negative
the limit is zero.

These are coordinate calculations for the boundary and ray limits in
Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics
426 (2023) 109107, equation (7.12), Proposition 7.8 and Lemma 7.11.

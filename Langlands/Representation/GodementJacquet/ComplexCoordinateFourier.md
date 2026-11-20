# Fourier inversion on finite complex coordinate spaces

`complexCoordinateFourier` uses the bilinear pairing `∑ᵢ yᵢ xᵢ` and one
self-dual scalar measure for each coordinate. Reindexing preserves both
the pairing and the product measure. This transports the Library's
Schwartz closure theorem from `Fin n` to arbitrary finite coordinate sets.

`integral_complexCoordinateFourier_zero` evaluates the integral of the
transform as the value of the original Schwartz function at zero.
The proof inducts on the index type. In the step, it separates one
coordinate, applies Fubini, and writes the inner function as a Schwartz
marginal weighted by the trace character in the other coordinates.
Scalar inversion evaluates this marginal at zero. The induction hypothesis
applies to the resulting Schwartz slice. The empty-coordinate case is
integration against a point mass.

This product inversion is used to handle Fourier marginals of the matrix
tests in complex Godement–Jacquet integrals.

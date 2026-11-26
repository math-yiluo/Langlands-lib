# Fourier closure of standard complex polynomial Gaussian tests

For a finite complex coordinate space the polynomial Gaussian class uses the real and imaginary coordinates and the factor `exp (-2π Σ |xᵢ|²)`. `ComplexStandardGaussianFourierStatement` asserts that the negative trace transform with the self-dual product measure preserves this class at any trace scale of unit modulus. Negating the trace scale gives closure for the positive split row transform. Flattening and restoring the matrix indices gives a standard square polynomial Gaussian representing the positive square Fourier integral.

The proof identifies each real coordinate with an inner product on the real Euclidean space underlying the complex coordinates. Fourier transformation there produces the reciprocal-scale Gaussian by `exists_polynomial_fourier`. The trace frequency multiplies the squared Euclidean norm by four and substitutes real-linear forms for the coordinates. This gives the Gaussian of the original scale and a new polynomial test.

These closure properties implement the choice of standard Gaussian in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), p. 10 and Proposition 8.1, pp. 60–61 of the author version, registered as `jacquet-2009-archimedean-rankin-selberg`, SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.

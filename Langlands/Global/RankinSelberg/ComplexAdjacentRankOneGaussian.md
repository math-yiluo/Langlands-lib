# Tate Gaussian products in the complex adjacent rank-one unfolding

`complexAdjacentRankOneGaussianProduct` proves `ComplexAdjacentRankOneGaussianProductStatement`. In the split Godement formula for `GL₂(ℂ) × GL₁(ℂ)`, take an angular Tate Gaussian as the square factor and use a row test whose positive Fourier transform is a nonzero scalar multiple of the angular Gaussian for the retained pair. The ordinary integral of the continued Godement coefficient is a nonzero constant times its pair L-factor on a right half-plane.

The proof uses the character law for the smaller Whittaker function to separate the unfolded kernel into two Tate integrals. It compares the square Haar measure with multiplicative Haar on `ℂˣ` through the determinant. The two angular Gaussians give the two Gamma factors of the prescribed character list. Compatibility of the quotient measure and nonvanishing of the two smaller coefficients make the remaining scalar nonzero.

This is the rank-one product case of Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.3, equation (8.3), author pp. 58–60, and Appendix §16, author pp. 109–110. The source is registered as `jacquet-2009-archimedean-rankin-selberg`, SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.

At trace parameter one, `splitRowTransform_one_rankOneRowGaussian` supplies the row test by exchanging the angular weights and multiplying by a power of the imaginary unit.

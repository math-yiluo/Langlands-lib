# Complementary triangular marginals for complex matrix Fourier transformation

`matrixTransform` implements Jacquet's square matrix Fourier transform with kernel evaluated at `−trace (Xᵀ Y)`. The measure is the product of the self-dual additive measures over all matrix entries. `upperMarginal` restricts the physical test to upper triangular matrices and integrates out their strictly upper entries. The resulting function of the diagonal is Schwartz.

`ComplexSquareFourierMarginalStatement` identifies the marginal of the matrix transform along the strictly lower entries of a lower triangular frequency matrix with the diagonal trace Fourier transform of `upperMarginal`. Each integrated entry in the two marginals carries the same self-dual measure.

The proof groups matrix coordinates into the diagonal and the two strictly triangular parts, indexed by strict upper pairs with transposition for the lower part. This gives a real linear isometry on the Euclidean parts. Fourier compatibility with the isometry yields the three-factor slice identity. The real frequency change on one triangular part contributes the inverse square of its self-dual density. That factor cancels the two triangular contributions in the square Fourier transform, with the diagonal transform and the two chosen marginal measures accounting for the remaining densities.

This identity is a derived step for the matrix-coefficient functional equation in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, equations (4.3) and (4.4), pp. 30–31.

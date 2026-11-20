# Duality of the complex Jacquet recursion integral

`complexJacquetRecursion` is the iterated integral in (7.8) of Jacquet's *Archimedean Rankin–Selberg Integrals* (2009), pp. 50–51, with `k = h⁻¹` in the actual left-unipotent quotient. Its determinant character includes any spectral twist of the final inducing character. The input function is assumed to satisfy the smaller-rank left Whittaker law. Multiplying the unipotent average by its value at `k` makes the kernel descend to the quotient.

`complexJacquetRecursion_dual` proves the change of variables of Proposition 7.3. The proof applies Lemma 7.1 to the rectangular test pulled back by `X ↦ k⁻¹ X g^ι`. Two-sided Fourier covariance contributes integer determinant powers, which combine with the half-rank exponents. The smaller Whittaker reflection is involutive and preserves the compatible quotient measure. The two Weyl determinants give the sign `η(-1)^(r+1)`.

This identity concerns the displayed iterated Bochner integrals. The identification of arbitrary standard-module Whittaker vectors with sums of such integrals and absolute convergence of the outer quotient integral are separate parts of the rank recursion.

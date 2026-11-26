# Last-row separation of standard square Gaussian tests

`complexSquareGaussianRowSplit` expresses each square polynomial Gaussian at scale \(2\pi\) as a finite sum of products of standard rectangular and row polynomial Gaussians. The rectangular factor uses all rows except the last. The row factor uses exactly the last row.

Each monomial splits into variables belonging to the two blocks, and the squared entry norm is the sum of the two squared norms. This factors the Gaussian and gives the claimed sum. Inverting the fixed scalar dilation in the polynomial multipliers realizes the factors as Schwartz tests at the same scale. This is the reverse passage from the matrix test to the separated inputs of Jacquet, *Archimedean Rankin–Selberg Integrals*, §8.2, equation (8.1).

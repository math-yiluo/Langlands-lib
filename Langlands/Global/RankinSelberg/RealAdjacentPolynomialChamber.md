# Real adjacent polynomial normalization in a strong chamber

`RealAdjacentPolynomialChamberStatement` assumes polynomial normalization
of the smaller equal-rank ordinary tests with standard Gaussian rows. It
uses a supplied compatible real quotient measure, a real additive parameter
of absolute value one, an upper spectral character list in the Godement
convergence chamber, and a lower character list of the indicated rank. For
each upper canonical Jacquet value and each lower value of a uniform
Whittaker intertwiner with the opposite character, the ordinary quotient
integral converges absolutely on a right half-plane. There it is a
polynomial times the reciprocal of the prescribed pair denominator.

The Godement sections of rectangular polynomial Gaussians span the upper
compact-finite principal series in the chamber. Dilation by `√π` on the
rectangle is right multiplication by the corresponding central scalar.
Right translation of the section and its left Borel covariance identify
the dilated section with a nonzero scalar multiple of the original one.
The dilated Gaussian has the standard scale, so the monomial decomposition
separates it into square and column tests. The canonical Jacquet map
agrees with the convergent integral and yields the separated Godement
coefficient on each summand. The self-dual Fourier transform keeps each
column factor in the standard polynomial Gaussian class. The separated
normalization theorem then applies, and the submodule of integrable
polynomial kernels gives the conclusion for all upper sections.

The square and smaller equal-rank factors follow the adjacent-rank step
in Jacquet, *Archimedean Rankin–Selberg Integrals*, §8.4, Proposition 8.1,
pp. 60–61. The chamber and the dilation transfer implement the Godement
realization of the compact-finite vectors in this calculation.

`sectionValue_standardMatrixTest` also gives the dilation comparison for
use in the equal-rank recursion. Its hypothesis is principal-series
membership of the undilated section. The scalar is the normalized Borel
character on the central matrix divided by the determinant weight on
that matrix.

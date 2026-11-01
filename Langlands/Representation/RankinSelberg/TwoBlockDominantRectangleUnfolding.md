# Product convergence for the actual rectangular section integrand

This derived helper forms the fixed-rectangle Whittaker restriction of a
larger-rank test and multiplies it by the actual scalar section and a continuous
weight on the standard unipotent quotient. Both descend to the actual block
unipotent quotient. The matrix is the published unequal-rank JPSS matrix,
with its supplied rectangular coordinate unchanged.

The published finite coefficient expansion gives a finite sum of separated
functions on the block quotient and rectangular space. If the supplied test
functional is zero, the same expansion is provided by the empty family. Each
diagonal coefficient has compact norm support on every determinant slice by
`diagonalWhittaker_slice_hasCompactSupport`. Ordinary absolute Jacquet
convergence and `sectionIntegrand_slice_unfolding` supply integrability of the
actual diagonal section product. The Schwartz rectangle factors are integrable
against the exact supplied scalar Haar product. Finite separated product
integrability therefore proves actual product convergence. The argument keeps
full Whittaker type, arbitrary complementary row sizes, independent universes,
and zero supplied functionals. It uses no epsilon equation.

This is internal analytic infrastructure for JPSS (1983), Sections 4.5, 4.6,
4.9 and 4.10(2), with the arbitrary complementary row and determinant-slice
packaging derived from the published support and finite-expansion route. It
asserts no lower-kernel convergence or final Laurent identity.
Source: `jpss-1983-rankin-selberg`, retained PDF SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

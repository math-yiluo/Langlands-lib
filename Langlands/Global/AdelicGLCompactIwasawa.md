# Compact diagonal parameters in adelic Iwasawa decomposition

`upperTriangularDiagonal` extracts the diagonal entries of an invertible
upper triangular adelic matrix as a tuple of ideles. The inverse diagonal
entries come from the inverse matrix, using `diagonalUnit`.
`continuous_upperTriangularDiagonal` proves continuity in the units topology
by checking both these entries and their inverses.

`isClosed_adelicUpperTriangular` records that the actual upper triangular
subgroup is closed: it is defined by vanishing of matrix entries below the
diagonal.

`exists_compact_iwasawaDiagonal` proves that every compact set C in the
actual adelic general linear group admits factorizations
g = u · diagonalGL(d) · k, where u is upper unitriangular, k belongs to the
standard compact subgroup, and every tuple d belongs to one compact set D.
There is no continuity assertion about a choice of the factors.

The proof applies the published adelic Iwasawa decomposition g = b · k.
Every such b lies in C times the inverse standard compact subgroup.
Its intersection with the closed upper triangular subgroup is compact.
The continuous diagonal extraction maps this intersection to the required
compact set D. Multiplying b by the inverse of its diagonal matrix produces
the unitriangular factor.

This is internal infrastructure derived from the existing Iwasawa theorem,
elementary triangular matrix identities, and compactness under continuous
maps. It does not assert an integration formula or an analytic estimate.

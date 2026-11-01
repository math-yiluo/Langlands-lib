# Compact inner determinant slices

This derived helper implements the fixed inner determinant slice used in
JPSS Section 6.3, printed pages 433–435, formulas (6), (8), and (9).
It does not prove joint convergence or interchange the two integration
variables.

For any prime, p-adic field in universe `uF`, and supplied topological data
`T`, `generalLinearDeterminantSlice T r m` is the subset of the actual
group `GL_(r+1)` on which `ord(det h)=m`. It is the inverse image of the
published determinant slice on the actual left unipotent quotient. It is
clopen and has normalized determinant absolute value `q^(-m)`.
The actual rank is positive, and `r=0` is included.

The compactness proof intersects the compact topological support of a
Schwartz–Bruhat test on the full square matrix space with the closed
condition `normalizedAbs(det A)=q^(-m)`. The latter constant is positive,
so the intersection consists of invertible matrices. The embedding of
the general linear group into full matrices therefore pulls this
compact set back to a compact group set. It contains the support of the
slice indicator times the restricted test.

`matrixSliceTest` packages that function as an actual Schwartz–Bruhat
function on the group. Its local constancy follows from the clopen slice
and the original locally constant matrix test.
`integrableOn_matrixSlice_mul` proves integrability of `Phi(h) f(h)` on
every slice for every continuous complex function `f` and every Borel
group measure finite on compact sets. It follows by multiplying the
compactly supported continuous group test by `f`. In particular this
does not assert global integrability near singular matrices.

The source is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Worker 486 visually read printed pages 432–436 (one-based PDF pages
67–71). The source uses the indicator of `ord(det(g*h))=m`; for a fixed
`g` this is the slice of `h` with order `m-ord(det g)`. The present
compactness argument is an internal justification for its inner
integrability. It is not stated as a separate lemma in the source.
No source-specific registered errata was found in the bounded project
checks recorded by the adjacent-rank development.

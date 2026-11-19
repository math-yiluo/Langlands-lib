# Compact Godement generation of the real two-character principal series

`RealGodementGLTwoGenerationStatement` expresses every smooth
vector of the two-character position principal series on `GL₂(ℝ)`
as a single compactly supported Godement section from the
trailing `GL₁(ℝ)` character. The lower-rank measure is Borel, finite
on compact sets, right invariant, and positive on nonempty open sets.

Take the normalized rectangular representative of the upper vector
and multiply it by a smooth bump in the squared row norm, supported
near norm square one. This yields a smooth test supported in a
compact annulus of full-row-rank matrices. The bump on the squared
absolute determinant of the lower-rank group has positive integral,
since it is continuous and equals one at the identity. Divide the
test by this integral.

At an orthogonal translating matrix, the squared norm of `(0,h)k`
is the squared absolute determinant of `h`. The matrix diagonal
with entries `1, det h` gives these bottom rows after multiplying
by `k`. The upper vector transforms by the trailing character
and the normalized absolute determinant shift `−1/2`. The
lower character is evaluated at `h⁻¹`, and the two Godement
determinant powers cancel the remaining factor. The integral is
therefore the original value on the compact subgroup, after the
bump normalization. Both functions belong to the same principal
series, so Iwasawa decomposition gives equality everywhere.

This proves the rank-two instance of the compact-support generation
in Jacquet Proposition 7.1(v), by a direct construction in the
upper triangular Borel convention.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, §7.1, pp. 43–46](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)

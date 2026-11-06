# Explicit opposite factors for quadratic root matrices

This module is an internal calculation in the existing `SU3Root.Parameters` coordinate group and its actual `GL₃` embedding. Its ring constructions use an arbitrary commutative ring with the specified involution. Its explicit factorization uses a field in arbitrary universe `u`, with no characteristic restriction.

`weylElement` is the existing Hermitian Gram matrix, viewed as an invertible matrix with itself as inverse. Entrywise multiplication proves the inverse identities. The module proves that this matrix squares to one, has determinant one, and preserves the specified Hermitian form. `oppositeEmbedding` is the upper-coordinate embedding conjugated by this involution. Its displayed matrix has lower adjacent entries `-bar(u)` and `-u`, and lower-left entry `v`.

For a scalar unit `t`, `reflectionMatrix c t` is `diagonal c t * weylElement`, where the diagonal construction is imported. Its only nonzero entries are `t` in position `(0,2)`, `-bar(t)/t` in position `(1,1)`, and `1/bar(t)` in position `(2,0)`. Its determinant is one. The ratio `reflectionMatrix c s * (reflectionMatrix c t)⁻¹` equals `diagonal c (s*t⁻¹)`; the proof cancels the two Weyl factors and applies the diagonal homomorphism laws.

For a coordinate parameter `x=(u,v)` with `v` nonzero, `leftOppositeParameter x` has coordinates `(u/bar(v),1/bar(v))` and `rightOppositeParameter x` has coordinates `(u/v,1/bar(v))`. Involutivity and the trace-norm equation `v+bar(v)=u*bar(u)` verify both parameter equations after clearing the nonzero denominators.

`opposite_factorization` proves the actual matrix equality

`oppositeEmbedding(leftOppositeParameter x) * embedding(x) * oppositeEmbedding(rightOppositeParameter x) = reflectionMatrix c (Units.mk0 v hv)`.

The proof uses injectivity of the value map on invertible matrices, expands each matrix entry, clears denominators and reduces the resulting polynomial equations to the defining trace-norm equation and its scalar multiples. These are direct consequences of the existing coordinate and matrix definitions; no additional literature theorem is assumed.

The result concerns the explicit coordinate model. It does not identify these coordinates or matrices with relative-root subgroups or normalizers of an arbitrary reductive group, establish opposite-factor-pair existence for such groups, determine primitive translation lattices, or prove full normalizer generation or the host facet-fixing statement.

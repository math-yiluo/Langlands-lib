# Opposite block parabolic geometry

This construction extends `Blocks` without changing its upper or opposite parabolic
subgroups, its ordered positive `BlockShape`, its standard coordinate numbering, or
its product of actual general linear groups `B.Levi R`. Worker 6 is the author.
It imports the independently published `Langlands.Group.GL.Blocks` construction.
This module supplies the lower-block constructions described below.

For every commutative ring `R`, `oppositeLeviProjection` extracts the actual diagonal
submatrices of a lower block triangular invertible matrix. Its inverse block is
extracted from the inverse of that same matrix. In the matrix product formula, a
summand from any other block is zero: below the selected index the second factor
vanishes, and above it the first factor vanishes. Thus diagonal extraction preserves
multiplication, and the two inverse identities follow from those of the ambient
matrix unit. No inverse, closure or decomposition law is assumed.

`oppositeLeviInParabolic` is the existing block diagonal embedding restricted to the
lower parabolic. Off-diagonal blocks vanish, and diagonal extraction of the section
is the identity. In particular `commonLeviEmbedding` identifies its ambient value
with the section of the upper parabolic; the two sides use the same Levi product
and the same matrix subgroup.

`oppositeUnipotentRadical` is the kernel of this actual projection, with Mathlib's
kernel normality instance. `oppositeUnipotentSubgroup` is its image under the
opposite parabolic's inclusion in `GL_n(R)`. Their membership characterizations
say precisely that the matrix is lower block triangular with identity diagonal
blocks. `oppositeLeviAction` is conjugation by the section on the normal kernel.
The unipotent component is `g * section(projection(g))⁻¹`. The resulting
`oppositeDecomposition` is an equivalence with radical times Levi, with inverse
`(u,m) ↦ u * section(m)`; it does not assert a direct-product group law.

The two conjugation-preservation proofs apply the corresponding upper or lower
projection to a conjugate and use its homomorphism laws and the split section.
Mathlib's `Subgroup.le_normalizer_iff` then proves that the common ambient
`leviSubgroup` normalizes each ambient radical.

For a topological commutative ring, all topologies are the inherited matrix-unit,
subgroup, and product topologies. Continuity of the opposite projection is checked
on the entries of both its values and inverses using `Units.continuous_iff`.
The section is continuous by the existing block embedding. Multiplication and
inversion make the constructed factorization a homeomorphism and make the
conjugation action jointly continuous. When `R` is Hausdorff, the kernel is closed
and its image is closed because the opposite parabolic inclusion is closed.
If the ambient actual general linear group is locally compact, these closed
inclusions give local compactness of the opposite radical.

The provenance is the same standard ordered block geometry documented in `Blocks`,
with the lower multiplication proof and explicit split-kernel construction given
above. This module does not prove parabolic quotient compactness, unipotent compact
exhaustion, Jacquet duality, or a modulus-character formula.

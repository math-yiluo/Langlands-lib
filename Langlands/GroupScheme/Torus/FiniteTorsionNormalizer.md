# Finite torsion subgroups detecting diagonalizable normalizers

This internal algebraic unit proves that some finite characteristic torsion
subgroup has exactly the full normalizer of an embedded diagonalizable group,
over every coefficient algebra. It assumes a corepresented ambient group
functor, a finitely generated abelian character group, and a finitely generated
ideal cutting out the embedded subgroup. Smoothness and a noetherian base are
not assumed.

`quotientEmbedding` constructs the natural injective character embedding
induced by a surjective quotient of character groups.
`integerTorsionEmbedding emb n` uses the characteristic quotient modulo
n-fold multiples. Its points are exactly the points of the original embedded
character group killed by raising to the n-th power. The proof factors a
character through the quotient exactly when it kills the multiple subgroup.
For positive n, this character quotient is finite by `FiniteCharacterSeparation`.

`exists_integerTorsion_same_normalizer` chooses a positive integer for which
the normalizer families coincide over every coefficient algebra.
`finiteTorsionNormalizerModel` records a choice of such an integer with this
property. The normalizer of the full character group preserves its n-torsion
subgroup because conjugation preserves powers and has an inverse.

For the converse, use the uniform finite character-degree normalizer test of
`FiniteTorsionNormalizerDetection`. Degree reduction of the universal conjugate
is exactly the universal conjugate of the integer-torsion embedding. Thus a
point normalizing this torsion embedding satisfies both finite-degree tests
and normalizes the full embedded group.

This proves equality of algebra-level all-refinement normalizer families. The
passage to scheme-level subgroup functors and the construction of a
normalizer homogeneous quotient remain separate assertions.

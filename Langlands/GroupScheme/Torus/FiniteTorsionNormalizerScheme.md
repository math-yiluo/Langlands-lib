# Scheme normalizers detected by finite diagonalizable subgroups

This internal unit proves that, over any affine base, a closed diagonalizable
subgroup of a smooth affine group has the same full scheme normalizer as one
of its finite characteristic torsion subgroups. The finitely generated
abelian character group may have torsion, the coefficient ring is arbitrary,
and normalizer equality holds on every relative scheme test.

`finiteTorsionNormalizerOverRing` chooses a positive integer n. Its associated
subgroup is the composite D(M/nM) → D(M) → G. The construction records that
this subgroup is closed, that its structure morphism is finite, and that its
normalizer subgroup functor equals the original normalizer subgroup functor.

The proof first identifies algebraic quotient-character embeddings with
actual diagonalizable group-scheme maps. Any quotient algebra cutting out a
closed diagonalizable subgroup is identified with its group algebra by
uniqueness of represented subgroups and the relative global-section
comparison. Thus the coordinate quotient is projective. When the ambient
coordinate algebra is finitely presented, the subgroup quotient is also
finitely presented, so the subgroup ideal is finitely generated.

The preceding algebraic finite-torsion normalizer theorem then chooses n
with equality of the normalizer families over all coefficient algebras.
Both actual normalizers have projective ideal cutouts, so the global-sections
membership criterion extends this equality from affine tests to arbitrary
scheme tests. Ambient coordinate isomorphisms transport the result to the
given smooth affine group. Surjectivity of M → M/nM makes the induced
subgroup map closed; finite generation of M and positivity of n make M/nM
finite, so the diagonalizable subgroup is finite over the original base.

This result reduces construction of a local normalizer quotient to the case
of a finite diagonalizable subgroup. It does not construct that homogeneous
quotient or claim the full multiplicative-type quotient theorem.

# Represented fppf quotients of groups of multiplicative type

Author: Worker 1467.

This internal derived development proves stability of the published
`IsMultiplicativeType` predicate under flat surjective homomorphisms locally
of finite presentation between actual group schemes over a field.

The quotient is first shown to be locally of finite type by descent along
the source cover. Its underlying space is quasi-compact by surjectivity
from the affine source, and its field-group structure gives separatedness.
The published affine quotient theorem then proves that its structure map
is affine.

After the given arbitrary splitting field extension, the source is an
actual diagonalizable group with finitely generated full character group.
Its coordinate pullback is injective by faithful flatness. Coefficient
contraction proves that the target coordinate Hopf algebra is spanned by
group-like elements. These elements form an abelian group embedded in the
original character group, so are finitely generated. The published
bialgebra reconstruction then yields an actual diagonalizable isomorphism.

`monomialGroupLikeAddEquiv` and `characterEmbedding` construct the character
comparison used in this proof. `IsMultiplicativeType.of_fppfHom` assembles
the argument. Arbitrary characteristic, arbitrary splitting extension and
character torsion are retained throughout.

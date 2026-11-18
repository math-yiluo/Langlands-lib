# Simultaneous algebraic envelopes for finite coordinate actions

`Langlands.GroupScheme.AbstractGroupTensorReduction.hasFiniteCoordinateEnvelopes`
proves `HasFiniteCoordinateEnvelopes k G` for any field `k` and abstract group
`G`, with independent universes. Given two homomorphisms to invertible matrices
in finite coordinates, it gives a reduced affine group scheme locally of finite
type over `k`, matrix representations in the two input dimensions, and a dense
family of rational points indexed by `G` whose matrices recover the two
homomorphisms.

`coordinateProductRationalEquiv` identifies the rational points of the actual
binary product of `GL (Fin n)` and `GL (Fin m)` with pairs of invertible
matrices in those dimensions. It combines the product point equivalence and
the general linear rational matrix equivalences.

The underlying scheme of this product is a pullback of affine schemes over
the ground field, so its structure morphism is affine. Each general linear
group is smooth, so `prop_tensor_hom` gives local finite type for the product.
The inverse of `coordinateProductRationalEquiv` carries the paired
homomorphism into its rational point group.

`RationalPointClosure.exists_dense_envelope` applies to the image subgroup of
that homomorphism. It gives a homomorphism from the reduced envelope to the
ambient product and a dense lift of the image subgroup. The surjective
homomorphism from `G` to its image reindexes the lift, so each point image
from the original family occurs in the resulting family. The two
representations are the restrictions of the categorical projections.
Composing each lifted point with the envelope map
recovers the original product point, and projecting its matrix coordinates
recovers the original input matrices.

This is an internal application of the Library's dense rational envelope,
product, and matrix representation APIs. It supplies the envelope hypothesis
of `abstractGroupTensorSemisimple_of_envelopes`.

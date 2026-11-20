# Direct product of complementary normal subgroups

`Langlands.GroupScheme.normalMultiplicativeUnipotentProduct` proves
`Langlands.GroupScheme.NormalMultiplicativeUnipotentProductStatement` at every
universe. It follows the proof of Lemma 16.44 on printed p. 340 of Milne's
*Algebraic Groups* (2017), registered as `milne-2017-algebraic-groups`
with SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

`unipotentMultiplicativeTriviality` gives disjoint subgroups of points on
every test scheme by Milne's Corollary 14.17, printed p. 284. Normality
then makes their elements commute. Disjointness also makes ordered
multiplication injective on points, since the two subgroup inclusions are
monomorphisms. This gives a group homomorphism `T × U ⟶ G` that is monic
as a morphism over the base.

`affineHomImage` factors this map through its closed image by a flat
surjective map locally of finite presentation. The image represents the fppf
product and is normal by normality of both factors. Quotient `G` by this
image to obtain an affine fppf quotient `G ⟶ C`. Its full kernel contains both
subgroup functors, so the map factors through each of `G ⟶ P` and `G ⟶ Q`
by `FppfHomDescent`.
The factor maps to `C` are flat, surjective and locally of finite
presentation by descent along the original quotient maps. Thus `C` inherits
unipotence from `P` and multiplicative type from `Q`.
`IsMultiplicativeType.hom_eq_zero_of_isUnipotent` makes every homomorphism
from a group of multiplicative type to an affine unipotent group zero.
Applied to the identity of `C`, this shows that `G ⟶ C` is zero. The
full-kernel condition gives a section of the monic closed image inclusion,
so the inclusion is an isomorphism. The map to
the image is flat, surjective, monic and quasi-compact, with
quasi-compactness from affineness of the source and image. It too is an
isomorphism, so the specified ordered multiplication is an isomorphism.

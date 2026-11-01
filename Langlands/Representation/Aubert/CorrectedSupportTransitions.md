# Actual cut maps on corrected support quotients

This internal construction joins the actual normalized cut maps to the corrected
support images. The source shapes `B,D` satisfy `B.cuts ⊆ D.cuts`; the Jacquet
target `C` stays fixed. All maps are on actual representations and actual
quotients. The coefficient and carrier universes are independent.

Adding source cuts decreases the block Weyl subgroup on the right of
`W_C \ W / W_B`. The subgroup antitonicity of the two-sided core therefore gives
`weylSupport B C θ ⊆ weylSupport D C θ`, and hence containment of the actual
matrix Bruhat supports.

`cutTermObject` is the genuine smooth object `i_B r_B A`, and
`cutJacquetObject` is `r_C i_B r_B A`. The actual cut transition evaluates
pointwise by the actual Jacquet quotient map. A nonzero target value forces a
nonzero source value. The source support condition and the preceding core
containment prove `cutMap_mem_correctedInductionSupport`.

`cutJacquetMap` is the normalized Jacquet descent of that same cut transition.
It sends the class of a supported function to the class of its actual cut image,
as stated by `cutJacquetMap_mk`. Every element of an actual support image has a
supported representative; the induction support result then proves
`cutJacquetMap_mem_correctedJacquetSupport`. This defines the equivariant
restriction `cutJacquetSupportMap`.

`cutSupportQuotientMap` descends this restriction to the actual quotient of the
upper support image by the pulled-back lower support image. Preservation holds
for both support sets, so the quotient universal property applies. The formula
`cutSupportQuotientMap_projection` identifies this map on all representatives.
For a successive filtration quotient one takes `θ ⊆ η`; the pulled-back quotient
construction itself does not require that containment.

The provenance is internal: the proofs combine the published block Weyl cut
correspondence, two-sided core containment, pointwise actual cut maps, normalized
Jacquet quotient representatives, and the existing actual support quotient API.
No orbital-integral comparison, exterior sign comparison, exactness or
concentration assertion is included in this module.

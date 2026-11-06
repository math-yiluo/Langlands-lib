# Literal domain transport through local extensions

This is an internal derived construction for connecting a finite cover of the
actual coproduct of two unchanged input algebras to the finite intersection
recognition interface. It uses full domains and the actual local-domain
extension and inclusion constructions. No additional literature result is
asserted.

For a full domain `S` in `U.algebra`, extension to the atlas has locus
`U.ambientMap '' S.locus`. The map `U.ambientMap` is injective, so taking the
relative domain of `U.extendInclusion S` recovers exactly `S.locus`. Its algebra
is definitionally `S.algebra` and its structural bounded map is `S.baseMap`.
The proof rewrites the extension locus and applies the injective
preimage-of-image identity.

`extendInclusion_product_locus` applies this identity to both factors in the
literal product locus. `pullback_extendInclusion_product_locus` takes the
inverse image along an arbitrary bounded coproduct map. Neither lemma requires
admissibility, spectral injectivity or ambient-map agreement of that map.

`FiniteIntersectionData.ofExtendedProductCover` takes full domains in the
unchanged input algebras, their extended local intersection pieces, bounded
local equivalences and exact equations for both original algebra legs. It also
takes the literal product-pullback loci of the cover members, the literal
intersection locus of each piece and their union equality. It composes the
piece inclusions with the extension inclusions and transports the cover-locus
equation by the preceding lemma. `ofProductCover` then derives global
ambient-map agreement and saturation from the finite local comparisons.

The constructor retains the candidate algebra, its two specified maps, the
finite cover and all local bounded equivalences. It does not construct the
global ideal, prove ideal-descent effectiveness or supply the required local
equivalences. It therefore remains a supporting construction toward
`SpecialSetIntersectionStatement`.

The coefficient, ambient-space and original-index universes are independent.
There is no nontrivial-valuation, strictness, reducedness, nonempty-domain or
global Hausdorff hypothesis.

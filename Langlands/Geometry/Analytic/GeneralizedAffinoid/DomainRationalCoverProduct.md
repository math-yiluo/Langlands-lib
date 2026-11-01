# Products of actual finite covers with supplied rational covers

Author: Worker 36.

This module constructs a common refinement of a supplied finite full-domain
cover `c : Domain.FiniteCover U` and a supplied finite ambient rational cover
`r : Domain.FiniteRationalCover U`. It proves that this concrete cover is
their binary product in the category of chosen refinements. The coefficient
field is any complete ultrametric normed field, and the underlying affinoid
algebras retain their finite positive-polyradius closed Tate quotient
presentations.

## Actual components and projections

`FiniteCover.rationalProduct c r` uses `FiniteCover.ofFintype` on the
finite type `Fin c.size × Fin r.size`. The component associated to `(i,j)`
is the already constructed full domain
`(c.obj i).rationalInter (r.chart j)`. Its algebra is the actual rational
coefficient-pullback quotient over `(c.obj i).algebra`; its locus is the
literal intersection of the two original component loci. Its restriction
to `U` is the left rational projection followed by `c.map i`.

For every point in `U.locus`, coverage by `c` chooses `i`, and coverage
by `r` chooses `j`. The point then belongs to the indicated intersection.
The number of components is `c.size * r.size`. Empty covers and empty
loci remain permitted. `rationalProductIndexEquiv` decodes the finite
ordinal component into the original pair, and `rationalProductIndex`
encodes a specified pair. The object, algebra and locus lemmas expose
the construction.

`rationalProductFst` and `rationalProductSnd` retain the two original
index choices. Their component arrows are respectively the actual
bounded structural map of the pulled rational quotient and the actual
bounded rational quotient transport. Both are refinements in the
original fixed ambient full-domain category.

## Product universal property and refinements

Given chosen refinements `f : b ⟶ c` and `g : b ⟶ r.toFiniteCover`,
`rationalProductLift f g` pairs the two chosen indices. On each component
it applies `Domain.rationalInterLift` to the original component arrows.
That lift constructs a bounded restriction through the full affinoid-test
representation of the intersection, using both image containments.
Transport along the finite-index equivalence only changes the component
index presentation.

The two projection equations first identify the decoded pair indices.
`Refinement.ext` then uses uniqueness of actual full-domain restrictions
to identify the whole arrows. Conversely, `rationalProduct_hom_ext`
extracts both coordinates from equal projected refinements. Injectivity
of the pair-index equivalence identifies the indices, and refinement
extensionality again identifies the actual arrows. In particular,
the proof does not treat the chosen-index refinement category as thin.

`rationalProductFan` stores the actual projections, and
`rationalProductFanIsLimit` packages the constructed lift, its two
factorization equations and its uniqueness as a binary product.

`rationalProductMap` acts on chosen refinements of both supplied covers.
The second input is any refinement between their underlying finite
covers. Composing with the two source projections and then applying the
constructed product lift supplies its actual bounded component arrows.
The projection equations express naturality. Product uniqueness proves
the identity and composition laws.

## Actual spectrum-cover diagrams

The two refinements induce continuous maps between the finite disjoint
unions of their actual representing spectra. The theorems
`rationalProduct_totalMap_fst` and `rationalProduct_totalMap_snd` state
that both projections commute with the original total spectrum-cover
maps to `U.locus`. They apply the published
`Refinement.spectrumMap_over_target`, which evaluates each actual
bounded restriction over the ambient algebra. No general representing
spectrum is identified with its locus.

## Source and scope

The original source is Vladimir Berkovich, *Non-archimedean analytic
spaces* (Trieste lectures, 2009), registered literature ID
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p. 9,
give the full affinoid-test representation, rational quotient domains
and intersection context. Definition 2.2.7, printed/PDF p. 10, gives
the affinoid-domain embedding category.

The common refinement and its chosen-index product universal property
are internally derived constructions from the implemented rational
intersections and finite-cover category. The module requires a supplied
finite rational cover; it does not prove its existence in
Gerritzen–Grauert Fact 2.2.5. It does not establish arbitrary full/full
intersection, general structural spectrum injectivity, an unrestricted
analytic atlas, Tate acyclicity, or an etale or equivariant etale site.

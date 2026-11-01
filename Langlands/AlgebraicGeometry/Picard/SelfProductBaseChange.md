# Self-products and actual base change

This internal categorical adapter compares the self-product of the actual
base change of `X → S` along `T → S` with the actual base change of
`X ×_S X`. It records the first projection as the canonical map induced by
the two base-change projections.

The map `selfProductBaseChangeMap` is the displayed `pullback.map`.
The isomorphism `selfProductBaseChangeIso` is constructed in both
directions by the pullback universal properties. Its inverse lifts the two
projections to `X` together with the common projection to `T`. The inverse
identities follow by checking the projections of each pullback.
The two `hom_fst` and `hom_snd` equations specify its projections.

In namespace `Langlands.AbelianScheme`, the constructions
`mumfordProductBaseChangeMap` and `mumfordProductBaseChangeIso` specialize
this comparison to the actual base-change functor and Mumford products.
The former is precisely the morphism `q` in
`ValuationRingTwoAxisExtensionStatement`; the theorem
`mumfordProductBaseChangeIso_hom_fst` identifies that map with the base-change
projection. No geometric hypothesis is used beyond the schemes and maps;
the specialization works for every abelian scheme over any base.

The provenance is internal: these are explicit composites of the existing
categorical pullback constructions, used to transport the final actual
bundle isomorphism. The module proves no bundle extension theorem.

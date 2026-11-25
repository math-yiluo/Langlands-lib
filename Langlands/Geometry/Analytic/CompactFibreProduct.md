# Finite chart covers and compactness of constructed fibre products

This is an internal consequence of the published
`AtlasTopology.CompactSubcover`, `FibreProductAtlas` and
`AnalyticFibreProduct` constructions. It supplies finite chart data and
compactness for the actual glued space; it assumes no categorical pullback
property.

For compatible strong maps `f : A → C` and `g : B → C`, where the atlas
presentations share field, space and chart-index universes, `FinitePairCover`
stores a finite set of actual `PairIndex f g` and an equality saying that
their chart ranges cover the entire glued space.

If the spaces of A and B are compact, the space of C is Hausdorff, and the
atlases of A and B contain all local domains,
`nonempty_finitePairCover` constructs such data and `finitePairCover` chooses
it. First the quasinet compact-subcover theorem supplies finitely many chart
ranges covering each factor. The proof retains an original chart index for
each range. For every pair of selected factor charts, the published
`FibreProduct.exists_finite_pairs` gives finitely many pair charts covering
the simultaneous inverse image of those ranges. Their finite union covers
the glued space, since every point has a projection into each factor.
Empty factors and empty selected families require no nonemptiness assumption.

`FinitePairCover.compactSpace` proves compactness by expressing the entire
space as a finite union of continuous images of compact affinoid spectra.
`FibreProduct.compactSpace` applies this to the constructed cover. These
compactness conclusions do not require either factor to be Hausdorff.

For saturated presentations with equal field, space and index universes,
`compactSpace_fibreProduct` applies the construction to `compatibleMap f`
and `compatibleMap g`. This specialization requires Hausdorff factors and
base, as does the published `fibreProduct` definition.
`isCompactSpace_localization_fibreProduct` combines compactness with the
published Hausdorff theorem for the glued space and the equality of the
underlying-space functors before and after localization. Its conclusion is
the published `IsCompactSpace` predicate, meaning compact and Hausdorff.

The intended use is geometric finiteness in the compact quasi-étale
comparison project. This module proves neither that the glued square is a
categorical pullback nor that its arrows are quasi-étale. It does not give
pullbacks of arbitrary localized morphisms, representability of presheaf
Čech nerve terms, or a compact basis for the quasi-étale site. Those
interfaces remain separate obligations.

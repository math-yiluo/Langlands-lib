# The affinoid atlas after extension of the ground field

`IndexedAffinoidAtlas.GroundFieldExtension.presentation K L a` is the
ground field extension of the presentation given by `a`. It is an
`AffinoidAtlasPresentation` on the quotient chart system of
`GroundFieldExtensionChartSystem`. The construction applies to every
indexed `K`-affinoid atlas over arbitrary complete ultrametric normed
fields `K` and `L` with `NormedAlgebra K L`. It includes trivial
valuations, all positive radii, nonreduced and zero algebras, empty
spectra and empty atlases.

`atlas` uses the original chart indices and their ground field extended
algebras. `AffinoidChartSystem.AtlasProjection.topology` supplies the chart
embeddings, local Hausdorffness and chart net. The theorem
`PresentedAffinoidAlgebra.GroundFieldExtension.spectrumProjection_surjective`
gives surjectivity on each chart, yielding `projection_image_chart`. This
and the preimage description `range_chart` give `range_chart_subset_iff`,
which recovers the original containments and proves distinctness of chart
ranges. For each containment the restriction is the scalar extension of
the corresponding original restriction. The quotient chart identities
give chart commutation, `restriction_represents` gives the universal
property against presented `L`-affinoid test algebras, and
`restriction_refl` and `restriction_trans` give the identity and
composition laws.

`projection` is the continuous quotient map to the original space. Its
value on each chart is the spectrum projection followed by the original
chart. `projection_surjective` follows from `projection_image_chart`
and the original net's covering property.

This presentation is a derived implementation of the ground field
extension in Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), §1.4, printed p. 30 (PDF p. 27), using the atlas
conventions of Definition 1.2.3 and Remark 1.2.4, printed p. 16
(PDF p. 13). The registered source is `berkovich-1993-etale-cohomology`.

Descent through quasi-isomorphisms to the localized category over `K`,
towers of field extensions, fiber products, and the comparison
`(X^an)_L = (X_L)^an` are reserved for Task 3519.

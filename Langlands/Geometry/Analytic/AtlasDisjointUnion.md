# Disjoint unions of arbitrary supplied affinoid atlases

Author: Worker 56. This is an internal construction from original indexed
atlases, `AtlasNonemptyCharts` and the sigma-family net construction.
No external theorem or original-literature claim is introduced.

Work over a complete normed ultrametric field `K`. The field, component-space,
chart-index and component-index universes are independent. The topology on the
total space is exactly the topological sigma construction on the original
component spaces. Original charts inside a component may overlap and may be
properly contained in one another. No directedness, global Hausdorffness,
reducedness, proper defining ideal or restriction to strict polyradii is assumed.

## Original nonempty charts

Given component atlases `a i` and the explicit hypothesis
`ha : ∀ i, (a i).HasNonemptyCharts`, `Index` is the sigma type of their original
chart indices. `algebra` is exactly the original presented algebra at that
index. `chart` composes the original chart embedding with the component's
actual sigma injection, and `range_chart` identifies its image.

`chart_subset_iff` identifies containment of two charts with the same tag
with containment of their original chart domains. It uses the injectivity of
the sigma injection. `tag_eq_of_subset` uses a point in the smaller chart to
prove that containment forces equality of component tags. It makes no claim
that the original chart indices are equal. For equality of chart domains,
`chartDomain_injective` first equates the tags and then applies the original
atlas's domain-injectivity law to the resulting equality of original domains.

`restriction` transports only the component tag along this proved equality
and then uses the original bounded restriction. `restriction_same` records
the exact original map when the tags are already equal. `restriction_chart`
applies the sigma injection to the original chart equation.
`restriction_universal` pulls membership in a sigma chart back to membership
in the original chart, then uses the original unique bounded factorization.
The test is every original `PresentedAffinoidAlgebra K`, including empty spectra,
nilpotents and arbitrary positive radii. `restriction_id` and
`restriction_comp` equate the actual bounded algebra maps by the original
component laws. No algebra-map equality is inferred from pointwise equality
on spectra.

`chartFamily_eq` identifies exactly the resulting chart family with
`AtlasTopology.sigmaFamily` of the original chart families.
`IsNet.sigmaFamily` therefore constructs its net condition from the component
nets. It allows empty intersections and arbitrary overlaps inside a component.
Local Hausdorff neighborhoods are the images of original local Hausdorff
neighborhoods under the open sigma injection. The genuine embedding-induced
subspace homeomorphism transports each Hausdorff structure.

`atlas` assembles these data into
`IndexedAffinoidAtlas.{u, max z v, max z w} K (Sigma X)`.
Its chart embeddings compose the original embeddings with sigma embeddings.
`atlas_hasNonemptyCharts` records that every original chart survives.
`atlas_algebra`, `atlas_chart` and `atlas_restriction_same` record the exact
original algebras, chart functions and same-component bounded restrictions.
`presentation` bundles this construction for a family of existing presentations
with nonempty charts.

## Arbitrary component atlases

`nonemptyAtlas` applies `nonemptySubatlas` to every arbitrary component atlas
and then applies `atlas`. The imported same-space construction proves the
necessary relative local refinement; no refinement or output atlas is assumed
here. Removing empty charts is necessary because the indexed-atlas signature
requires chart domains to distinguish indices: empty domains from different
components would otherwise coincide.

The component spaces and their topologies are unchanged. The new index is a
component tag together with an original chart index and its nonemptiness
witness. The retained algebras, embeddings and bounded restrictions are the
original ones, as `nonemptyAtlas_algebra` and `nonemptyAtlas_chart` record.
`nonemptyAtlas_hasNonemptyCharts` proves the output condition.
`nonemptyPresentation` bundles this construction on the same actual sigma
space for every family of existing presentations.

An empty component may contribute no chart, and the component-index type may
itself be empty. No ambient-space nonemptiness assumption is needed.
This unit constructs atlases and presentations. Complete maps between these
disjoint unions, their categorical universal property, arbitrary-source
induction, refinement localization, analytic action continuity and analytic
sites remain separate obligations.

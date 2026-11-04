# Actual finite local-domain covers by common original charts

Work over any complete ultrametric normed field `K`, with an existing
`IndexedAffinoidAtlas K X` on an arbitrary topological space. The original
algebras are finite positive-polyradius affinoid presentations, and the original
bounded restrictions represent full affinoid domains. No directedness or greatest
chart hypothesis is added.

`CompactIntersectionChartCover i j S` stores a finite list of original chart
indices. Each listed chart domain is contained in both original chart domains
`i` and `j`, and their union covers `S`. `compactIntersectionChartCover`
constructs this data for every compact subset of the intersection. The net
intersection axiom gives a quasinet in the actual intersection subspace. The
helper `IsNet.exists_finite_cover_of_subset_inter` provides a finite cover by
contained original members. Choosing their original indices and enumerating the
finite family gives the stated data. The record is an output of this construction,
not an assumed atlas extension.

For a full domain `U` over the algebra of chart `i`, its ambient image
`a.chart i '' U.locus` is compact. If it lies in original chart `j`,
`domainImageChartCover` therefore constructs the preceding data for that image.

For any such constructed finite common-chart family `c`, `c.domainCover` is an
actual `Domain.FiniteCover U`. Its member at `t` is the full represented domain

```
U.inter (a.restrictionDomain (c.index t) i (c.left_subset t)).
```

Its algebra is the actual pushout quotient used by `Domain.inter`. Its covering
arrow is the original left quotient projection. The intersection locus is exactly
`U.locus` intersected with the inverse image of the selected original chart
domain under `a.chart i`. Pointwise coverage follows from the finite chart cover.
`localDomainChartCover` supplies this actual cover directly from `U` and its
containment in chart `j`.

`domainCoverToChart` retains the other original quotient projection. Localization
along the original contained chart then constructs `domainOverChart`, a full
domain over the selected common chart with exactly the same intersection algebra.
Its structural map is the second quotient projection, and composition with the
original atlas restriction is the original intersection structural map.
Extension through the selected chart's containment in `j` constructs
`domainOverRightChart`, again retaining the same algebra. The two
`chart_image_...` results prove that these transported domains have precisely
the same ambient subset as the original intersection, and in particular lie
inside the ambient image of `U`.

All finite families may be empty when coverage allows it. The construction adds
no nonempty-spectrum, reducedness, strictness or nontrivial-valuation premise.
It does not yet glue the transported structural maps into a single bounded map,
prove unrestricted representation over chart `j`, or construct unrestricted
analytic atlases and sites.

This is an internal derivation from the existing net, original full-domain
restriction, full-domain intersection, compactness and localization APIs. The
paired `AtlasTopology/CompactSubcover` helper documents the finite compact-cover
argument. No new original-literature assertion or external construction is used.

# Finite selected-chart refinements of arbitrary recognized subsets

Author: Worker 36.

For a locally refining selection of original charts, this module constructs
a finite cover of every original recognized affinoid subset by actual
full domains whose algebras and ambient maps are charts of the selected
atlas's local-domain saturation. The parent algebra and its embedded
ambient chart remain those of the given recognized subset.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i) and (iii),
printed p.21 / PDF p.18. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The cited original page was read for this construction; no source-specific
errata file was found in the available Library location.

Part (i) proves invariance of the completed domain family under a subnet
by finding finite subordinate covers. Part (iii) flattens successive
finite special coverings. This module combines those two construction
patterns under the explicit `IsLocallyRefiningSelection` hypothesis.
Its chosen presentations and full structural maps are internal
infrastructure, rather than a separately stated result of the source.
The imported finite realization of each original local domain supplies
the inner covers; the given recognized subset supplies the outer cover.
Neither recognition in the selected saturation nor an algebra comparison
is assumed as an output witness.

## Successive full-domain covers

Write `b = a.subatlas P hP`, with
`hP : a.IsLocallyRefiningSelection P`, and let
`V : a.saturatedAtlas.RecognizedSubset`. Its defining finite special
cover has original saturated chart indices `i`. Each defining component
is an actual full domain over `V.algebra`, with algebra the corresponding
original saturated chart algebra.

`subatlasRecognitionLocalParent` chooses the actual original local-domain
representative of each such saturated chart.
`subatlasRecognitionInnerGluing` uses the constructed finite selected-chart
cover of that representative. The existing local-domain realization
construction gives `subatlasRecognitionInnerRealization`. Its parent
algebra is definitionally the algebra of the outer component.

`SubatlasRecognitionComponentIndex` is the finite dependent family of
pairs `(i, j)`, where `i` selects an outer component and `j` an inner
component of its realization. `subatlasRecognitionComponent` extends
the inner full domain through the actual outer full domain. The extension
retains the inner algebra; it composes the two full bounded structural
maps. The declarations ending in `_algebra` and `_baseMap` record these
definitional identities.

`subatlasRecognitionComponent_over_ambient` proves that composing this
extended domain's spectrum map with `V.chart` gives exactly the selected
saturated chart. The spectrum map of an extension is the composite of
the spectrum maps of its two domains. The outer component's chart
equation and the inner realization's chart equation therefore give the
claimed equality.

`subatlasRecognitionComponent_locus` identifies the exact locus as

```text
V.chart ⁻¹' range (b.saturatedAtlas.chart innerIndex).
```

The forward direction uses the component's full representation and its
ambient equation. In the reverse direction, injectivity of `V.chart`
identifies an alleged preimage with the image of the given chart point.
The full representation then supplies membership. This uses injectivity
on spectrum points only to identify points and subsets.

## The flattened finite cover

`subatlasRecognitionComponentEnumeration` identifies the dependent finite
family with a finite ordinal.
`subatlasRecognitionDomainCover` packages the extended full domains into
an actual `Domain.FiniteCover (Domain.whole K V.algebra)`.
Its arrows store their full bounded structural maps.

For coverage, the proof first chooses an outer component containing
an arbitrary point of the parent spectrum. The outer representation
supplies a point of its algebra spectrum. The inner realization's full
domain cover then chooses an inner component containing that point.
The locus formula for extension places the original point in the
extended component. Reindexing the pair by the finite ordinal completes
the coverage proof.

`subatlasRecognitionChartIndex` retains the corresponding selected
saturated chart index for each flattened component.
`subatlasRecognitionDomainCover_obj_algebra`,
`subatlasRecognitionDomainCover_over_ambient`, and
`subatlasRecognitionDomainCover_obj_locus` give the exact component
algebra, ambient map and preimage locus formulas.

`subatlasRecognitionChartIndex_covers` proves that the union of these
finitely many selected saturated chart ranges equals the original literal
`V.locus`. A chart point maps into `V.locus` by the ambient equation.
Conversely, the original recognized chart covers `V.locus`, and the
constructed full-domain cover covers every point of its spectrum.
The component preimage locus equation yields membership in one selected
chart range. `subatlasRecognitionChartIndex_subset` extracts each
individual range containment.

## Hypotheses and scope

The field is complete and ultrametric; its valuation may be trivial.
The field, ambient space and original index have independent universes.
No global Hausdorffness, reducedness, nonzero-algebra or nonempty-cover
hypothesis is added. The given object is an actual recognized subset
of the original saturated atlas, and local refinement is the stated
input about selected original charts.

This unit constructs actual finite full-domain components, their bounded
maps and coverage. It does not yet compare their full maps with canonical
restrictions for all contained selected saturated charts, construct
finite overlap gluing and admissibility for this arbitrary `V`, or
recognize `V` in the selected saturation. Those are subsequent steps.
Arbitrary equivalent-net invariance, maximal-atlas uniqueness, analytic
morphism comparison, analytic etale and equivariant sites, and the
Harris specialization remain further obligations of the host task.

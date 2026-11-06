# Actual finite original-chart refinement after iterated recognition

Author: Worker 36.

This module constructs a finite full-domain cover of an affinoid chart
obtained by iterating full recognition. Every flattened component retains
an actual chart algebra from the first saturated atlas, its complete
bounded structural map, its full represented-domain universal property
and its exact original ambient chart. The finite ambient chart union is
exactly the iterated chart's unchanged literal locus.

The source motivation is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), the special-cover equalizer following
Lemma 1.2.12, printed p.20 / PDF p.17, and the recognition construction and
Proposition 1.2.13(iii), printed p.21 / PDF p.18. In the proof of (iii),
finite defining covers are refined and then flattened to obtain a cover
from the earlier atlas. Registered source
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These original pages were read for this construction. No source-specific
errata file was found in the available project and Library locations.

This is a derived finite-refinement step toward actual idempotence.
It works directly with full domain presentations and their composed
bounded maps. It does not assume that the entire iterated chart is
already recognized for the first saturated atlas, nor does it assume a
realization or specialness of the flattened covering.

Put `B = a.fullRecognitionAtlas` and let
`W : B.saturatedAtlas.RecognizedSubset`. Thus `W` is an actual chart
index of `B.fullRecognitionAtlas`. Its recognition witness supplies
outer full domains `Cᵢ` over `W.algebra`, with algebras equal to the
corresponding chart algebras of `B.saturatedAtlas`.
`iteratedRecognitionLocalParent i`, denoted `Uᵢ`, is the actual chosen
local-domain representative of that outer saturated chart. Its original
index is a chart of `B`, hence a recognized chart over `a.saturatedAtlas`.
Its full domain has exactly the outer component algebra.

The already constructed realization of every full domain in a recognized
chart therefore applies to `Uᵢ.domain` in `Uᵢ.index`.
`iteratedRecognitionInnerGluing i` and
`iteratedRecognitionInnerRealization i` instantiate that actual
construction. They provide finitely many original
`a.saturatedAtlas` chart indices and full domains over `Uᵢ.algebra`,
with the original chosen component algebras unchanged. The inner
realization's parent algebra is the outer component algebra and its
ambient chart is exactly `Uᵢ.ambientMap`.

`IteratedRecognitionComponentIndex` is the finite dependent family of
pairs `(i,j)`, with `i` an outer index and `j` an inner index for that
particular component. For such a pair,
`iteratedRecognitionComponent` extends the inner full domain through
the actual outer full domain `Cᵢ`. This constructs a full domain over
`W.algebra`; it is not an arbitrary subset assigned an affinoid structure.
Its algebra is literally the original inner saturated-chart algebra,
as its algebra theorem records.

`iteratedRecognitionComponent_baseMap` displays the complete bounded
structural map as the inner restriction composed with `Cᵢ.baseMap`.
The imported full-domain extension theorem proves the represented-domain
universal property of this composite, including unique bounded
factorization for every presented affinoid test algebra.

`iteratedRecognitionComponent_over_ambient` proves that the actual
spectrum map recovers the original inner saturated chart under `W.chart`.
The spectrum map of the structural composite is first identified with
the composition of the two actual spectrum maps. The outer recognition
chart formula then recovers `Uᵢ.ambientMap`, and the inner realization's
chart formula recovers the original `a.saturatedAtlas` chart.

`iteratedRecognitionComponent_locus` proves that the full domain's
locus is exactly the inverse image, under `W.chart`, of that original
chart range. The forward inclusion uses the full representation's range
identity and the ambient chart formula. The reverse inclusion uses
injectivity of `W.chart` to recover the actual spectrum point and then
applies the full representation's image condition.

`iteratedRecognitionComponentEnumeration` reindexes the finite dependent
family by `Fin` of its actual finite cardinality.
`iteratedRecognitionDomainCover` packages the components as an actual
`Domain.FiniteCover (Domain.whole K W.algebra)`. Its inclusion maps store
the complete composed structural bounded maps.

Coverage is proved from the two actual finite covers. Given a parent
spectrum point, the outer recognition cover supplies an outer full domain
containing it; the full range identity supplies a spectrum point above it.
The inner realization cover supplies a full domain containing that point.
The original parent point therefore lies in the image locus of the
extended inner domain. The finite enumeration then supplies its
flattened index. No finite subcover is extracted from an arbitrary
compact covering.

`iteratedRecognitionChartIndex` records the retained original
`a.saturatedAtlas` chart index of each enumerated component.
The cover algebra theorem states literal equality with that chart's
algebra. The cover ambient and locus theorems record the exact original
chart recovery and inverse-image locus after enumeration.
Finally, `iteratedRecognitionChartIndex_covers` proves

```text
⋃ k, range (a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W k))
  = W.locus.
```

The forward inclusion comes from the actual component spectrum maps
under `W.chart`; the reverse uses its range identity and the constructed
full-domain cover.

The coefficient-field, ambient-space and original-index universes remain
independent. The complete ultrametric field may have trivial valuation.
There is no ambient Hausdorff, reducedness, nonzero-algebra or
nonempty-cover hypothesis. Empty finite dependent families and empty
spectra remain allowed.

This unit constructs the actual finite refinement with complete maps
and full representations. It does not yet construct the flattened
pairwise overlap charts, prove their completed-tensor specialness, or
recognize the whole iterated chart relative to the first saturated atlas.
Recognition idempotence, equivalent-net invariance, maximal-atlas
uniqueness and unrestricted analytic morphism identification remain
later obligations. The general special-intersection lemma and
closed-ideal effectiveness are not assumed.

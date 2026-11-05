# Actual inverse images inside source local affinoid domains

Let `K` be a complete ultrametric normed field, let `A` and `B` be actual
affinoid-atlas presentations, and let `f : StrongHom A B`. The ambient-space
universe `v` and original chart-index universe `w` remain independent. Trivial
valuations are allowed. Fix an actual source local domain `U`, an original
target chart `j`, and the containment
`f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)`.
Only the image of this local domain must lie in `j`; the image of its whole
original parent chart need not do so. No saturation, directedness, coherence,
or quasi-isomorphism hypothesis is used.

## Constructed domain and exact locus

The previously constructed `f.localChartPullback U j h` is a bounded map from
the algebra of chart `j` to the stored algebra of `U`. For every actual full
domain `V` of chart `j`, `localDomainInverseImage` first applies the actual
`Domain.pullback` construction to this map and `V`, then extends that full
domain through `U.domain` into the original source chart `U.index`.

The stored algebra is exactly
`AffinoidPushout.algebra (f.localChartPullback U j h) V.baseMap`.
The pullback's first bounded quotient leg has the full representation property
against every presented affinoid test, by `Domain.pullback`. Unconditional
domain extension proves the resulting full representation over the original
source chart and retains this actual algebra. Neither the new algebra nor its
representation is an input hypothesis.

`localDomainInverseImage_locus_image` identifies the ambient locus with the
image under `U.ambientMap` of the exact spectrum inverse image of `V.locus`.
`localDomainInverseImage_locus` then proves that this is precisely

`U.locus ∩ f.baseMap ⁻¹' (B.atlas.chart j '' V.locus)`.

For the forward inclusion, the local bounded map's chart equation sends every
point to the displayed target locus. For the reverse inclusion, the exact
range of `U.ambientMap` supplies a source spectrum point. Injectivity of the
original target chart identifies its local-map image with the supplied point
of `V.locus`. This identifies loci without using spectrum actions to identify
bounded algebra maps.

## Bounded maps, restrictions and spectrum squares

`localDomainInverseImageInclusion` is the actual arrow into `U` obtained from
domain extension and the existing same-chart functor into the category of
source local domains. Its restriction is exactly the first structural leg of
the pullback domain.

`localDomainInverseImageMap` is the second bounded quotient leg from the
stored algebra of `V` to the new algebra. The theorem
`localDomainInverseImageMap_comp_baseMap` is the complete bounded pushout
square with `V.baseMap`, the local bounded map, and the preceding inclusion.
`localDomainInverseImage_ambientMap` expresses the new ambient map through
`U.ambientMap` and the pullback's first spectrum projection.
`localDomainInverseImageMap_chart` proves that the second projection commutes
with `f.baseMap` and the actual ambient map of the target local domain
`⟨j,V⟩`. These spectrum equations follow from the existing bounded-map square
and extension formula.

`localDomainInverseImageFunctor` is the composite of `Domain.pullbackFunctor`,
`U.domain.extendFunctor` and `LocalDomain.sameChartFunctor`. Its objects are
exactly the constructed local inverse images. Its arrow restrictions are the
actual bounded pushout lifts `Domain.pullbackRestriction`; the displayed
target square retains the complete original bounded restriction of every
target arrow. The inherited functor laws concern actual local-domain arrows.

## Finite covers and provenance

For every actual `Domain.FiniteCover V`,
`localDomainInverseImageCover` pulls the cover back and extends it through
`U.domain`, using the proved injectivity of that domain's spectrum map.
It retains the original finite size. Its members are exactly the constructed
inverse-image domains of the original members, and its arrow restrictions
equal those given by `localDomainInverseImageFunctor`. The final covering
theorem proves that their ambient loci cover the entire constructed inverse
image inside `U`. Empty finite covers are included by the same construction.

This is an internal consequence of the existing local bounded-map
construction, actual affinoid pushout and full-domain pullback, unconditional
domain extension, and finite-cover transport. It makes no new original-source
attribution. It constructs inverse images for a fixed source local domain and
one containing original target chart. Comparisons under changes of source
domain or target parent chart, global source-atlas refinements, Ore squares,
identification of the presentation localization with the intended analytic
category, analytic and equivariant sites, and Harris specializations remain
further obligations.

# Actual direct images of local full domains under full quasi-isomorphisms

This module constructs direct images in the actual local full-domain
categories of affinoid atlas presentations. It retains each source domain's
presented quotient algebra and, under the stated coherence law, every original
bounded restriction. Its namespace is
`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso`.

## Parameters and hypotheses

The field `K : Type u` has instances `NormedField`, `IsUltrametricDist`, and
`CompleteSpace`. The ambient-space universe `v` and chart-index universe `w`
are independent. There is no nontrivial-valuation premise.

Let `f : StrongHom A B`. The assumption `hf : f.IsQuasiIso` consists of an
ambient homeomorphism and a full affinoid-domain representation by the actual
bounded pullback at every admissible pair of original charts. Full
representation includes unique bounded factorization for every presented
affinoid coefficient algebra. A `LocalDomain A.atlas` stores an original
parent index and a full domain over that parent's algebra.

Constructing image objects needs only `hf`. Constructing the functor also
requires `hc : f.HasCoherentPullbacks`, the existing intrinsic coefficient-test
law on the original supplied pullbacks. This law quantifies over arbitrary
presented affinoid coefficient algebras and compatible factorizations through
common target charts. It assumes no direct-image maps or functor.

The final original-chart comparison additionally assumes
`hb : B.atlas.HasAllLocalDomains`. This is equality of the target local-domain
locus family with its original chart-range family. It is already proved for
the constructed saturated atlas; it is an explicit hypothesis here for a
general target atlas.

## Image objects and their complete structural maps

For a source local domain `U`, choose the original target chart
`f.chosenTargetIndex U.index` containing the entire image of its parent chart.
The existing `hf.localDomain` represents that parent image with the literal
source parent algebra and the original bounded pullback. `domainImage U`
extends `U.domain` through this full domain using `Domain.extend`.

Consequently `domainImage_algebra` is literal equality with `U.algebra`, and
`domainImage_baseMap` is the actual composite

```text
U.domain.baseMap.comp
  (f.pullback U.index (f.chosenTargetIndex U.index) admissibility).
```

Full-domain extension is available without an extra spectral-injectivity
premise because the embedding theorem is already proved for every full
domain. `domainImage_ambientMap` follows from the original chart square
evaluated at `U.domain.spectrumMap x`. Taking ranges and using
`LocalDomain.range_ambientMap` proves

```text
(hf.domainImage U).locus = f.baseMap '' U.locus.
```

For every original target chart containing this locus,
`domainImage_chartRestriction` identifies the entire bounded structural map
with `f.localChartPullback U j hU`. This follows directly from
`domainChartRestriction_eq_changeMapChart`: the image domain has exactly the
same algebra and composite parent map used by that chart-change construction.
The two explicit containment proofs `h` and `hU` express the same containment
using the two equal locus descriptions.

## The actual fully faithful functor

For `p : U ⟶ V`, `domainImageMap hc p` has containment obtained by applying
`Set.image_mono` to `p.subset` and has restriction exactly `p.restriction`.
For every original target chart containing both image loci, the complete
structural equation follows by the preceding chart-restriction identification
and `localChartPullback_source hc`. Thus the arrow belongs to the actual
`LocalDomain B.atlas` category, including all its chart equations.

`domainImageFunctor hc` uses these objects and arrows. Identity and composition
hold by extensionality of the stored bounded maps. No directedness, source
closure, target closure, or atlas-refinement premise is required.

The ambient homeomorphism is injective, so `domainImage_subset_iff` reflects
as well as preserves containment. `fullyFaithfulDomainImageFunctor` constructs
a preimage arrow from that reflected containment using
`LocalDomain.Inclusion.ofSubset`. Both inverse laws use the existing uniqueness
of actual inclusion arrows, which was proved from full-domain universal
properties. The module provides the resulting `Full` and `Faithful` instances.
It does not infer equality of bounded algebra maps merely from equality on
spectrum points.

The comparisons with `LocalDomain.toAffinoidSpace`,
`LocalDomain.toTopologicalSpace`, and the contravariant
`LocalDomain.boundedPresheaf` are literal functor equalities. They hold because
both the quotient algebras and the complete bounded restrictions are retained.

## Original target charts and bounded comparisons

Under `hb`, `imageOriginalChartIndex hb U` applies the existing
`domainChartIndex` to the constructed image domain. Its original chart range
is the entire subset `f.baseMap '' U.locus`.

`imageOriginalChartDomainIso` is an isomorphism over the chosen target parent
algebra between the constructed image domain and the original target
restriction domain. It uses `chartDomainIso`, whose two bounded maps are
constructed from full-domain universal properties in both directions.
`imageOriginalChartBoundedEquiv` therefore gives an actual
`BoundedAlgEquiv K U.algebra (B.atlas.algebra imageIndex)`. Its forward map is
the restriction of the inverse space arrow.

`imageOriginalChartBoundedEquiv_comp_baseMap` proves that this forward bounded
map, composed with the actual composite image base map, equals the original
target atlas restriction from the chosen parent to the image chart. The proof
is the inverse domain arrow's structural equation. No isometry or norm-one
bound is asserted.

## Provenance and remaining scope

This is internal derived content. It combines the existing full
quasi-isomorphism local representation, unconditional domain extension, full
domain chart-change identity, coherent source naturality, actual local-domain
category, and original-chart comparison construction. The equations and
universal properties just described construct all new objects and arrows.
No new external-literature assertion or source quotation is made.

This unit does not prove essential surjectivity of the image functor,
construct Ore squares for arbitrary target quasi-isomorphisms, identify the
full analytic morphism category, or define the analytic and equivariant sites
and Harris tower specializations. Those obligations of the host task remain.

# Original-domain transport by actual chosen atlas isomorphisms

Author: Worker 56.

Let `K : Type u` be a complete ultrametric normed field and let
`A,B : AffinoidAtlasPresentation.{u,v,w} K`. This module starts with a full
isomorphism `e : A ≅ B` in the published category of monotone chosen atlas
maps. It constructs an equivalence between their actual original-domain
inclusion categories and proves preservation and reflection of the existing
quasinet topology. Field, point and chart-index universes remain independent.

## Internal provenance

This is an internal consequence of the published chosen atlas category,
original-domain category and topology, and the homeomorphism invariance of
restricted quasinets. Those dependencies are imported by Lean name.
`Hom.image_chart_subset` supplies actual image containment, while equality of
the complete chosen arrows supplies the two inverse index laws.
`AtlasTopology.IsQuasinet.imageFamily_restricted` transports the domain
condition using the actual induced subspace topology.

No independent source theorem is claimed. The proofs below explain the
derivation from those constructions. The input isomorphism retains all bounded
pullbacks and their restriction equations. Extracting its topological and
index consequences does not identify bounded maps by their spectral points
or impose reducedness on any affinoid algebra.

## Base homeomorphism and exact chart images

`isoHomeomorph e` applies the existing space functor to `e` and uses
`TopCat.homeoOfIso`. Its forward and inverse functions are exactly
`e.hom.baseMap` and `e.inv.baseMap`. The evaluation and symmetry lemmas expose
these functions.

`iso_hom_inv_indexMap` and `iso_inv_hom_indexMap` apply evaluation of the
chosen index function to the two categorical inverse equations. The resulting
inverse index functions form `isoIndexEquiv e`. These inverse equations follow
from equality of the entire chosen arrows; they are not additional inputs.

`isoHomeomorph_image_chart` proves that the image of the whole range of chart
`i` is exactly the range of the selected target chart `e.hom.indexMap i`.
Forward containment is the existing chart formula. For reverse containment,
apply the inverse arrow's image containment to a target point. Its inverse
image lies in the chart selected by the inverse index function. The first
index inverse equation identifies that chart with `i`. The base homeomorphism's
inverse equation then recovers the target point. Surjectivity of the chosen
index function proves `isoHomeomorph_image_chartFamily`, identifying the entire
target chart family with the image of the entire source family.

## Actual image domains

`isoHomeomorph_isOriginalChartDomain` transports the source contained-chart
quasinet to the actual image subset, then rewrites its image chart family as
the target's original chart family. Applying the same construction to `e.symm`
and using inverse image cancellation gives
`isoHomeomorph_isOriginalChartDomain_iff`.

`isoOriginalDomain e S` bundles the actual subset `isoHomeomorph e '' S`
and the constructed domain-condition proof. No domain or target atlas is
assumed on this image subset. `isoOriginalDomainOrderIso e` uses image by
the inverse homeomorphism for its inverse, set-image cancellation for its
inverse laws, and injectivity for reflection of subset inclusion. In particular,
it is an order isomorphism for the original subset orders. The formula
`isoOriginalDomain_ofChart` recovers the selected original target chart exactly.

The selected entry `isoOriginalDomainEquivalence e` is the categorical
equivalence induced by this order isomorphism. It sends objects to their actual
image subsets and arrows to their subset inclusions. Each object continues to
have the actual subspace affinoid presentation already constructed by the
original-domain machinery.

## Arbitrary covering families and sieves

For every independently indexed family `D i` of domains included in `S`,
`isoOriginalDomain_imageFamily` identifies the family of their actual image
subsets with the image family of their source subsets.
`isoOriginalDomain_ofArrows_mem_iff` preserves and reflects the condition that
their generated sieve covers. It applies the existing characterization of
covering families as quasinets on the actual target subspace, the preceding
image-family equality, and the restricted-family homeomorphism formula.
Homeomorphism invariance of the quasinet condition gives the equivalence.
The finite-neighborhood requirement is retained in full.

`isoOriginalDomain_functorPushforward_mem_iff` treats every sieve, using
Mathlib's expression of an arbitrary sieve as a generated family of arrows and
its formula for the functorial pushforward of that family.
`isoOriginalDomain_functorPullback_mem_iff` applies this result to the
functorial pullback; the full and essentially surjective image functor has
pushforward of pullback equal to the original sieve, by the existing Galois
insertion. Thus both functorial operations preserve and reflect covering.

`isoOriginalDomain_coverPreserving` packages preservation in Mathlib's
`CoverPreserving` predicate. `isoOriginalDomain_isCocontinuous` packages the
covering-pullback result in `Functor.IsCocontinuous`.
`isoOriginalDomain_isContinuous` combines cover preservation with the
existing compatible-family preservation of a representably flat functor;
an equivalence supplies the latter hypothesis. It therefore provides
Mathlib's continuity condition for sheaf precomposition on these sites.

## Scope and empty cases

Empty spaces, domains, chart families and covering families remain permitted.
All image and inverse laws hold in those cases, and the quasinet arguments
use the existing relative-neighborhood condition without choosing an ambient
point or adding any nonemptiness assumption.

The input must be an actual isomorphism of the chosen atlas category.
The module proves invariance of the fixed-original-chart sites under such
isomorphisms. It does not establish comparison under arbitrary refinements,
identify these objects with all analytic domains, assert analyticity of an
arbitrary homeomorphism between supplied atlases, construct a full analytic
or etale site, or construct the Harris tower. No particular sheaf-category
equivalence or locally constant coefficient comparison is bundled here.

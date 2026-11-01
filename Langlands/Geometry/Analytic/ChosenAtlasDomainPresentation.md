# Actual bounded presentation transport of original domains

Author: Worker 56.

Let `K : Type u` be a complete ultrametric normed field,
`A,B : AffinoidAtlasPresentation.{u,v,w} K`, and `e : A ≅ B` a full
isomorphism in the category of monotone chosen atlas maps. For every actual
original-chart domain `S` of `A`, this module constructs

```text
A.originalDomainPresentation S ≅
  B.originalDomainPresentation (isoOriginalDomain e S).
```

The isomorphisms commute with actual ambient inclusions and are natural in all
original-domain inclusions. Field, point and chart-index universes remain
independent.

## Internal provenance

This is an internal construction from the existing domain realizations and
complete chosen-arrow codomain factorization. It imports
`ChosenAtlasDomainTransport` for the actual image domain, base homeomorphism,
exact whole-chart image equation and image-domain categorical equivalence.
It imports `OriginalDomainPullbacks` for `Hom.factorOriginalDomain` and
`originalDomainInclusion_mono`. No new literature theorem is asserted.

The latter monicity result concerns entire chosen arrows. It recovers base
maps and indices by subtype extensionality and recovers dependent bounded
pullbacks by heterogeneous congruence, since composing with an ambient
inclusion's bounded identities retains those maps. Consequently the
cancellation arguments here preserve all algebra data. They do not infer
algebra-map equality from equality of spectral points and do not assume
reducedness.

## The actual restricted maps

`isoOriginalDomainHomeomorph e S` is Mathlib's image restriction of the actual
base homeomorphism `isoHomeomorph e`. Its forward function applies
`e.hom.baseMap` and its inverse applies `e.inv.baseMap`, with their codomains
restricted to the actual subspaces. The two evaluation lemmas record the
underlying ambient point values.

`isoOriginalDomainMap_chart_subset` proves that each whole selected target
chart of `A.originalDomainInclusion S ≫ e.hom` lies in the image domain.
The source chart lies in `S` by its retained-index subtype condition.
The exact whole-chart image formula identifies its image with the selected
target chart. Set-image monotonicity proves containment.
`isoOriginalDomainMap` factors this complete ambient composite through the
actual image-domain presentation using `Hom.factorOriginalDomain`.

For the inverse composite
`B.originalDomainInclusion (isoOriginalDomain e S) ≫ e.inv`,
`isoOriginalDomainInverse_chart_subset` applies the exact whole-chart formula
to `e.symm`, takes the inverse image of the retained target-chart containment,
and cancels the image followed by inverse image. Its selected whole source
charts therefore lie in `S`. `isoOriginalDomainInverse` factors this composite
through the original presentation of `S`.

The point, index and pullback evaluation lemmas expose both constructions.
The forward map applies `e.hom.baseMap`, selects `e.hom.indexMap c.val`,
and retains exactly `e.hom.pullback c.val`. The inverse uses the corresponding
data of `e.inv`. The factorization inherits monotonicity, the chart equation
and the equality of bounded restriction squares from the ambient composites.
No bounded pullback or target atlas on the image is assumed as an additional
input.

## Full inverse laws and inclusion compatibility

`isoOriginalDomainMap_inclusion` and
`isoOriginalDomainInverse_inclusion` recover the two complete ambient
composites after inclusion. These are the published codomain factorization
equations.

`isoOriginalDomainMap_inverse_id` composes the forward and inverse maps with
the source domain's ambient inclusion. Associativity and the two preceding
equations reduce this composite to the source inclusion followed by
`e.hom ≫ e.inv`. The input isomorphism's complete inverse law makes this the
source inclusion. Cancelling its monomorphism proves equality with the
identity as a complete chosen bounded arrow.
`isoOriginalDomainInverse_map_id` uses the same argument with the image-domain
inclusion and `e.inv ≫ e.hom`.

`isoOriginalDomainPresentation e S` bundles exactly these two constructed
maps and their full inverse laws. The equation
`isoOriginalDomainPresentation_homeomorph` identifies the base homeomorphism
of this presentation isomorphism with the actual restricted homeomorphism
defined above. It follows by pointwise extensionality.

## Naturality

`isoOriginalDomain_mono` records image monotonicity with the actual image
domains as its source and target. For every `h : S ≤ T`,
`isoOriginalDomainMap_naturality` states that source inclusion followed by
transport to the image of `T` equals transport of `S` followed by image-domain
inclusion. After composing with the image of `T`'s ambient inclusion, both
arrows reduce to `A.originalDomainInclusion S ≫ e.hom`. Monicity proves the
equality. `isoOriginalDomainInverse_naturality` proves the inverse square
using the ambient inclusion of `T` and `e.inv`.

The selected entry `isoOriginalDomainPresentationNatIso` packages these
components and the forward naturality equation as

```text
A.originalDomainFunctor ≅
  (isoOriginalDomainEquivalence e).functor ⋙ B.originalDomainFunctor.
```

Both diagrams take values in the actual category of chosen bounded atlas
presentations, and their arrows retain the complete bounded pullbacks.

## Scope and empty cases

Empty spaces and domains remain permitted. Containment, factorization,
homeomorphism restriction and categorical cancellation add no nonemptiness
assumptions. No strict-radius or nontrivial-valuation hypothesis is added.

The input is a full chosen atlas isomorphism. These results concern actual
original-chart domains of those fixed presentations. They do not construct
analyticity from an arbitrary homeomorphism, invariance under arbitrary
refinements, saturated atlases, arbitrary analytic domains, full analytic or
etale sites, or the Harris tower. Concrete locally constant section transport
and general sheaf-category comparisons are separate constructions.

# Étaleness of the inclusions of the pieces of a disjoint union

This internal module proves that, in the localized category of analytic spaces,
the inclusion of each piece of the chosen disjoint union
`localizedSigmaCofan` is étale for the actual `etale` predicate of the
analytic étale site. It also proves a general criterion: a domain embedding
whose image is open maps to an étale arrow. All results are derived
infrastructure for the étale-site statements about disjoint unions and
induced spaces. They have no separate literature source. The coefficient
field is any complete ultrametric normed field.

## Domain embeddings onto a domain

`SaturatedAtlasPresentation.isQuasiIso_domainFactor` takes a strong map
`f : A ⟶ B` of saturated presentations with `hf : f.IsDomainEmbedding`, and
an original chart domain `S` of `B`. It assumes that `f.baseMap` lands in
`S` and that every point of `S` is in its image. Under these hypotheses
the corestriction `domainFactor f S himage`
(`SaturatedDomainCorestriction`) is a strong quasi-isomorphism. Here the
source is the refining subpresentation of the charts sent into charts
inside `S`, and the target is `B.originalDomain S`.

- Its base map is the codomain restriction of an embedding, and it is
  surjective onto `S`. So it is a homeomorphism
  (`isHomeomorph_iff_isEmbedding_surjective`).
- On an admissible chart pair its relative image locus equals the relative
  image locus of `f` on the underlying charts, which a direct set-theoretic
  computation checks. Its bounded pullback is the pullback of `f`, so it
  represents this locus by `hf`, with admissibility transferred by
  `domainBaseMap_admissible_iff`.

## Open domain embeddings are étale

`SaturatedAtlasPresentation.etale_localizationFunctor_map_of_isDomainEmbedding`
states: for a domain embedding `f : A ⟶ B` between saturated presentations
with equal space and chart-index universes, whose base map has open range,
the arrow `localizationFunctor.map f` is étale. Take the open domain
`D := B.openDomain (range f.baseMap) hU`. The identity
`domainFactor_comp_inclusion` gives the factorization

`L f = (L r)⁻¹ ≫ L (domainFactor f D) ≫ L (B.originalDomainInclusion D)`,

where `r` is the refining subatlas inclusion
(`isQuasiIso_refiningSubatlasInclusion`), and the right-hand side is
rewritten with `localizedQuasiIso_hom`. The first factor is an
isomorphism. The second is the image of a quasi-isomorphism by
`isQuasiIso_domainFactor`. Both are étale by `etale_of_isIso`. The last
factor is étale by the published open-domain theorem
`etaleOpenDomainStatement`. Then `etale_comp` composes the three.

## Pieces of a disjoint union

`SaturatedAtlasPresentation.etale_localizedSigmaCofan_inj X j` states that
for every family `X : J → LocalizedCategory K` and `j : J`, the inclusion
`(localizedSigmaCofan X).inj j` is étale. The proof unfolds
this inclusion: with `T j := localizedObjectEquiv.symm (X j)`, it is
the inverse of the localized nonempty-replacement isomorphism of `T j`,
followed by `localizationFunctor.map ((sigmaCofan T).inj j)`. The
first factor is étale by `etale_of_isIso`. The second is étale by the
previous criterion, which applies by two facts. First,
`isDomainEmbedding_sigmaCofan_inj` (`DisjointUnionDomainEmbeddings`) makes
the saturated inclusion a domain embedding. Second, its range, the range of
`Sigma.mk j`, is open (`isOpen_range_sigmaMk`).

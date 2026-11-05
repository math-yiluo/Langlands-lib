# Bounded naturality of actual local-domain inverse images

This internal construction extends
[StrongLocalDomainInverseImage](StrongLocalDomainInverseImage.md).
The base field is a complete ultrametric normed field; trivial valuations are
allowed. The ambient-space universe `v` and original chart-index universe `w`
are independent. The input is an actual strong map `f : StrongHom A B`
between affinoid-atlas presentations.

For source and target local domains `U` and `V`, suppose that the image of
`U.locus` lies in the original parent chart of `V`. Write `D(U,V)` for the
existing `localDomainInverseImage U V.index h V.domain`. Its actual algebra
is the affinoid pushout from that construction, and its ambient locus is

```text
U.locus ∩ f.baseMap ⁻¹' V.locus.
```

The parent containment does not require all of `f(U.locus)` to lie in
`V.locus`. Both local domains can use arbitrary original parent charts.
The domains fully represent their loci: their universal properties test
unique bounded factorizations against every presented affinoid algebra.

## Identification of the second bounded leg

`localDomainInverseImage_image_subset` proves that `f(D(U,V).locus)` is
contained in `V.locus`, using the exact locus formula.
Consequently the previously constructed `localDomainPullback D(U,V) V`
is available.

`localDomainInverseImageMap_eq_localDomainPullback` identifies this map
with the actual second pushout leg. This identification requires the existing
intrinsic condition `f.HasCoherentPullbacks` on the original supplied
pullbacks. The proof applies `localDomainPullback_unique`, uses the entire
bounded pushout square, and then applies `localChartPullback_source` to the
actual inclusion `D(U,V) ⟶ U`. Thus the equality is derived from full-domain
uniqueness and bounded structural equations. It is not inferred from the
induced functions on spectra.

## Restrictions across both parent charts

For actual inclusions `p : U ⟶ U'` and `q : V ⟶ V'`, with the parent
containment at both endpoints, `localDomainInverseImageRestriction` constructs
an actual inclusion

```text
r : D(U,V) ⟶ D(U',V').
```

The exact locus formula and the two given containments provide its ambient
containment. `LocalDomain.Inclusion.ofSubset` constructs the entire bounded
restriction, retaining its equations over every containing original chart.

`localDomainInverseImageRestriction_source` proves the source triangle
`r ≫ i' = i ≫ p`. Here `i` and `i'` are the actual first-leg inclusions
into `U` and `U'`. The local-domain category is thin because of its proved
full-test uniqueness. Applying the restriction field to this equality proves
`localDomainInverseImageRestriction_comp_source`, the complete equation

```text
r.restriction.comp i'.restriction = i.restriction.comp p.restriction.
```

These constructions and the source equation need no coherence premise.
With `f.HasCoherentPullbacks`,
`localDomainInverseImageRestriction_comp_target` proves

```text
r.restriction.comp m' = m.comp q.restriction,
```

where `m` and `m'` are the actual second pushout legs. It rewrites them by
the preceding full-map identification and applies the existing two-variable
`localDomainPullback_naturality`. Both `p` and `q` can cross original parent
charts.

## The functor of admissible domain pairs

`localInverseImageProperty` is the parent-containment predicate on
`LocalDomain A.atlas × LocalDomain B.atlas`.
`LocalInverseImageData` is its full subcategory, so its arrows are precisely
pairs of actual local-domain inclusions. `localInverseImageSource` and
`localInverseImageTarget` retain the respective domains and arrows.

`localInverseImageFunctor` sends a pair to the actual domain `D(U,V)` and
an arrow to the constructed restriction above. Identity and composition
follow from full-test uniqueness in the local-domain category.
`localInverseImageFunctor_obj` gives the unchanged constructed object, and
`localInverseImageFunctor_locus` gives its exact ambient intersection.

`localInverseImageSourceInclusion` is a natural transformation to the source
projection, using the actual first legs and requiring no coherence.
Under the intrinsic coherence condition, `localInverseImageTargetMap` is a
natural transformation from the inverse-image functor to the target
projection after applying the respective `LocalDomain.toAffinoidSpace`
functors. Its components are the opposites of the actual second bounded
legs. Its naturality is the complete bounded target equation above, passed
through `Quiver.Hom.op`.

## Equal-locus comparisons and scope

`localDomainInverseImageIso` constructs an actual isomorphism if the two
source loci agree and the two target loci agree. The exact intersection
formulas imply equal inverse-image loci, and the existing `isoOfLocusEq`
constructs mutually inverse actual bounded restrictions.
`localDomainInverseImageIso_hom` identifies its forward map with the
functorial restriction induced by the source and target equal-locus
isomorphisms. These comparisons require no coherence.

The provenance is internal: the new content combines the constructed
pushout domain, its bounded structural square, the existing local-domain
restriction category and the coherent local-domain pullback equations.
No inverse-image object, comparison, representation or naturality output
is assumed. This unit establishes local restriction comparisons; constructing
global atlas refinements and Ore squares, identifying the intended analytic
category, and constructing the analytic and equivariant sites and Harris
specializations remain further obligations.

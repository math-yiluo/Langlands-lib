# Intrinsic and ambient rational sections under full-domain localization

Author: Worker 36.

Let `K` be a complete ultrametric normed field, `A` an actual
positive-polyradius presented affinoid algebra, and `d : Domain K A`
a full represented affinoid domain. This module identifies the sheaf of
intrinsic compatible rational quotient sections over `d.algebra` with the
sheaf of ambient compatible rational sections on the finite full-domain
site localized at `d`. It also constructs the comparison for the inverse
site equivalence. All maps act on actual quotient elements.

## Relative domain values

For a slice object `U : Over d`, the intrinsic domain
`d.relativeFunctor.obj U` has algebra `U.left.algebra`, structural map
`U.hom.restriction`, and locus the full inverse image of `U.left.locus`
under `d.spectrumMap`. Its intrinsic rational charts are charts over
`d.algebra`; the ambient rational charts on `U.left.locus` are charts
over `A`. These indexing families need not coincide.

`relativeLocusSectionsEquiv d U` is the canonical algebra equivalence

```text
OpenSections.Sections (d.relativeFunctor.obj U).locus
  ≃ₐ[K] OpenSections.Sections U.left.locus.
```

It first applies the inverse of the intrinsic `locusSectionsEquiv` to
recover an element of the unchanged stored algebra, then applies the
ambient `locusSectionsEquiv`. The forward and inverse application lemmas
state these two compositions exactly. The two inverse laws follow from
those of the composed algebra equivalences.

`relativeLocusSectionsEquiv_toLocusSections` shows that the intrinsic
family of an element `a : U.left.algebra` becomes its ambient family.
`fromLocusSections_relativeLocusSectionsEquiv` shows that recovery of the
ambient family yields the same stored element as intrinsic recovery.
Both follow directly from the already proved recovery identities.

`relativeLocusSectionsEquiv_chart` identifies every resulting ambient
chart component: it is the actual bounded restriction from
`U.left.algebra` to that ambient rational quotient, applied to the
recovered intrinsic element. Thus the comparison does not discard
nilpotents or replace sections by spectral point values.

`relativeLocusSectionsEquiv_fromBase` retains the structural map from
`d.algebra`. The intrinsic family of a base element `a` becomes
`toLocusSections U.left (U.hom.restriction a)`. The proof writes the
intrinsic base family using `toLocusSections_baseMap` and applies the
preceding stored-element identity.

## Forward presheaf and sheaf comparison

`relativeLocusSectionsEquiv_restriction` quantifies over every slice
arrow `f : U ⟶ V`. Comparing intrinsic sections before or after
restriction gives the same ambient family. The proof uses naturality
of recovery, the definitional retention of `f.left.restriction` by
`relativeFunctor`, and naturality of the forward section comparison.

`relativeLocusSectionPresheafIso d` packages these equivalences as

```text
d.relativeFunctor.op ⋙ locusSectionPresheaf K d.algebra
  ≅ (Over.forget d).op ⋙ locusSectionPresheaf K A.
```

Its naturality is the preceding restriction identity; its two component
application lemmas expose the same algebra equivalence and its inverse.

`relativeLocusSectionSheaf d` is the image of the actual intrinsic
`locusSectionSheaf K d.algebra` under the proved equivalence
`d.localizationSheafEquivalence (CommAlgCat K)`.
`localizationLocusSectionSheafIso d` identifies this sheaf with
`(locusSectionSheaf K A).over d`. Their underlying presheaves are exactly
the source and target above, so `ObjectProperty.isoMk` lifts the
constructed natural isomorphism. Its forward and inverse component
formulas remain the stated relative algebra comparisons.

## Extension and return comparison

For `U : Domain K d.algebra`, `d.extend U` has exactly `U.algebra` as its
algebra and `d.spectrumMap '' U.locus` as its ambient locus.
`extendLocusSectionsEquiv d U` is

```text
OpenSections.Sections U.locus
  ≃ₐ[K] OpenSections.Sections (d.extend U).locus.
```

It recovers an element intrinsically and forms its ambient family.
The inverse recovers the ambient element and forms its intrinsic
family. The forward and inverse application lemmas, preservation of
stored-element families, recovery identity, and every-ambient-chart
component formula record these operations explicitly.

`extendLocusSectionsEquiv_fromBase` shows that an intrinsic base family
of `a : d.algebra` becomes the ambient family of
`(d.extendInclusion U).restriction a`, which is literally `U.baseMap a`.
`extendLocusSectionsEquiv_restriction` proves naturality under every
inner domain arrow, using the original bounded restriction retained by
`extendFunctor`.

`extendLocusSectionPresheafIso d` packages the inverse of these value
equivalences as

```text
d.extendOverFunctor.op ⋙ (Over.forget d).op ⋙ locusSectionPresheaf K A
  ≅ locusSectionPresheaf K d.algebra.
```

The final `inverseLocalizationLocusSectionSheafIso d` lifts this natural
isomorphism to the inverse finite-site transport of the ambient
localized compatible-section sheaf and the intrinsic sheaf. The
presheaf and sheaf component application lemmas fix the direction:
their forward map is the inverse of `extendLocusSectionsEquiv`, and
their inverse map is that equivalence itself.

## Provenance and scope

This is an internal consequence of `DomainOpenSections`,
`DomainAlgebraSheafLocalization`, `DomainRelativeRepresentation`,
`DomainLocalization`, and `DomainSiteLocalization`.
They supply the canonical algebra and compatible-family equivalences,
their actual restriction naturality, the unchanged algebras and
bounded arrows under localization, and the equivalence of the two
independently constructed finite-domain sites. Composing the algebra
equivalences, using their inverse laws, and bundling the resulting
natural maps proves this unit. No new original-literature assertion,
assumed analytic comparison, or private peer draft is used.

The construction allows arbitrary positive radii, trivial valuations,
nonreduced and zero algebras, empty spectra and permitted empty finite
covers. It concerns compatible sections on represented subsets and
the finite point-covering site of full represented domains. It does
not identify an ordinary inverse-image sheaf on a closed domain with
the intrinsic structure sheaf. Ordinary-open locally ringed-space
restriction comparisons, unrestricted atlases, analytic etale and
quasi-etale sites, equivariant sites and Harris towers remain separate
construction obligations.

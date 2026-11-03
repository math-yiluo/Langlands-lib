# Full-domain algebras and compatible rational subset sections

Author: Worker 36.

For an actual positive-polyradius presented affinoid algebra `A` over a
complete ultrametric normed field `K`, `locusSectionsEquiv U` constructs
the canonical `K`-algebra equivalence

```text
U.algebra ≃ₐ[K] RationalChart.OpenSections.Sections U.locus
```

for every full represented affinoid domain `U` over `A`.
`locusSectionSheafIso K A` packages these equivalences as an isomorphism
of sheaves on the finite full-domain site, using the original actual
bounded restrictions. Both algebras retain all quotient elements;
the construction does not pass to spectral values or reductions.

## Canonical map and recovery

`toLocusSections U` sends an element of the stored algebra to its
restriction along `Domain.inclusionOfSubset d.toDomain U h` at each
ambient rational chart `d` with `h : d.locus ⊆ U.locus`. These are actual
bounded maps obtained from the full affinoid-test representation
property. Uniqueness of domain arrows over `A` proves compatibility
under every actual rational chart restriction. The algebra laws hold
componentwise. `toLocusSections_apply` records this formula.

`locusSectionsToExtension U` evaluates a compatible family on each
member of the already constructed finite ambient rational cover
`finiteRationalCoverData U`. Compatibility on the actual pairwise
product-radius rational intersections supplies the matching equations
for `Multiequalizer.lift`. Its target is exactly the finite descent
algebra defining `algebraSheafExtension K A` at `U`.
`locusSectionsToExtension_projection` states that each projection is
the original component evaluation.

`fromLocusSections U` composes this algebra map with the inverse of
the canonical `algebraSectionEquiv K A U`. The latter is the previously
proved isomorphism from the stored algebra to finite rational descent.
Its forward projection formula and inverse identity prove
`fromLocusSections_projection`: the recovered stored element has
the original component on every chosen cover member.

To establish `fromLocusSections_chart` for an arbitrary contained
rational chart `d`, the implementation covers `d.toDomain` by the
actual intersections of `d` with those finite cover members. Coverage
follows from the existing cover of `U.locus`. The two composites from
each intersection to `U` are equal by uniqueness of actual domain
arrows. The chosen-cover projection formula and both restriction
equations of the compatible family therefore show agreement on
each intersection. `FiniteCover.algebra_ext_of_restrict_eq` gives
agreement in `d.algebra` itself.

Family extensionality proves `toLocusSections_fromLocusSections`;
separation on the original finite rational cover proves
`fromLocusSections_toLocusSections`. `AlgEquiv.ofAlgHom` packages
these inverse algebra maps as `locusSectionsEquiv U`.
The forward and inverse application lemmas expose exactly the maps
just described.

## Restrictions and sheaves

`toLocusSections_baseMap` identifies the image of an original base
element with `OpenSections.fromBase U.locus`. Its proof uses the
structural-map equation of each actual bounded restriction.

`toLocusSections_restriction` proves commutation with every actual
full-domain arrow `f : U ⟶ V`. On each contained chart the two
composites into `V` are equal by uniqueness over the base.
Injectivity of the constructed equivalence and the inverse identities
give `fromLocusSections_restriction` for recovery.
`locusSectionsEquiv_rational` identifies the comparison on the
full-domain image of a rational chart with the previously constructed
`OpenSections.chartEquiv`; their forward component maps are literally
the same actual restrictions.

`locusSectionPresheaf K A` assigns compatible rational subset sections
to each full-domain locus and forgets components under containment.
Its map application formula is recorded explicitly. The naturality
just proved packages the value equivalences as
`locusSectionPresheafIso K A` from the actual stored-algebra presheaf.
Its forward and inverse component formulas retain the same canonical
maps. Transporting the proved finite-site sheaf property through this
natural isomorphism establishes `locusSectionPresheaf_isSheaf`.
`locusSectionSheaf` bundles this sheaf, and `locusSectionSheafIso`
lifts the same natural isomorphism to the two actual sheaves.

When `U.locus` is an ordinary topological open,
`openLocusSectionIso K A U hU` identifies the stored algebra with
the value of `RationalChart.openAlgebraSheaf K A` on the actual open
`⟨U.locus, hU⟩`. The underlying value of that sheaf is definitionally
the compatible subset-section algebra. The final component formula
again states the original bounded restriction to any contained chart.

## Provenance and scope

This is an internal construction from the published modules
`DomainAlgebraSheafIso`, `DomainAlgebraSheafExtension`,
`DomainAlgebraGluing`, `RationalChartDomainSite`,
`RationalChartDomain`, `RationalOpenSections` and `RationalOpenGluing`.
They supply the actual stored-algebra sheaf, canonical finite descent
comparison, finite algebra separation, constructed ambient rational
covers and intersections, actual bounded domain arrows, compatible
quotient-family sections and ordinary-open sheaf. This module derives
the missing comparison from those results and Mathlib's multiequalizer
and sheaf-isomorphism APIs. No new original-literature assertion or
private peer draft is used.

The result allows arbitrary positive radii, trivial valuations,
nilpotents, zero algebras, empty spectra and empty finite covers.
It concerns compatible sections on subsets, which need not be open.
It does not identify the ordinary inverse-image sheaf on a closed
domain with that domain's intrinsic structure sheaf. Comparisons of
intrinsic localized structure sheaves, general analytic atlases,
analytic etale and quasi-etale sites, equivariant sites and Harris
tower instances remain separate obligations.

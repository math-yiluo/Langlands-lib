# Compatible quotient sections on subsets of a full domain

Author: Worker 36.

Let `K` be a complete ultrametric normed field, `A` an actual presented
positive-polyradius affinoid algebra, and `d : Domain K A` a full represented
affinoid domain. This module constructs an algebra equivalence between actual
ambient compatible rational quotient sections on every subset `S ⊆ d.locus`
and intrinsic compatible rational quotient sections on `d.spectrumMap ⁻¹' S`.
The subset need not be open or itself represented by a domain.

## Evaluation on full domains

`sectionEvaluation U hU` evaluates a compatible family on any full domain `U`
whose locus is contained in the family's indexing subset. It first restricts
the family to `U.locus`, then applies the canonical `fromLocusSections U`.
It is a `K`-algebra homomorphism to the actual stored algebra `U.algebra`.

`sectionEvaluation_restriction` says that first restricting the indexing
subset does not change this evaluation. `sectionEvaluation_naturality`
quantifies over every actual full-domain arrow `f : U ⟶ V`: applying the
original bounded restriction `f.restriction` to evaluation on `V` equals
evaluation on `U`. Its proof uses the published restriction naturality of
full-domain recovery and composition of component-forgetting restrictions.

`sectionEvaluation_rational` identifies evaluation on a contained rational
chart with the original family component in its actual quotient algebra.
The proof specializes `locusSectionsEquiv` to `OpenSections.chartEquiv`.
`sectionEvaluation_fromBase` retains the actual structural image of each
base algebra element, using the forward/recovery inverse identity.

## Intrinsic and ambient maps

For every ambient subset `S`, `toIntrinsicSections d S` is

```text
OpenSections.Sections S →ₐ[K]
  OpenSections.Sections (d.spectrumMap ⁻¹' S).
```

Its component on an intrinsic rational chart `e` evaluates the ambient
family on the full domain `d.extend e.toDomain`. The helper
`extend_locus_subset_of_preimage` proves the required image containment.
Compatibility under every intrinsic rational restriction follows from
evaluation naturality after the actual `extendFunctor`; that functor retains
the original bounded restriction. `AlgHom.pi` and `codRestrict` supply the
algebra laws without replacing any quotient algebra.

`relativeMap d f hU hV` is the relative inclusion attached to any ambient
arrow `f : U ⟶ V` between domains contained in `d`. Its restriction is exactly
`f.restriction`. Uniqueness of actual ambient inclusions into `d` proves its
over-base equation, including the entire bounded-map triangle.

For `hS : S ⊆ d.locus`, `fromIntrinsicSections d hS` goes in the reverse
direction. On an ambient rational chart `e` contained in `S`, it evaluates
the intrinsic family on

```text
d.relative e.toDomain
  (inclusionOfSubset e.toDomain d (e.property.trans hS)).
```

`relative_locus_subset_preimage` places this full domain inside the relevant
intrinsic subset. Compatibility follows from evaluation naturality along
`relativeMap`, again with the original bounded restrictions. Both application
lemmas expose these precise component formulas.

## Domain evaluations and inverse laws

`sectionEvaluation_toIntrinsicSections` holds for every intrinsic full
domain `U` contained in the preimage of `S`. Evaluating the constructed
intrinsic family on `U` equals evaluating the original ambient family on
`d.extend U`, in their identical stored algebra. The proof applies injectivity
of `locusSectionsEquiv U`, unfolds the recovery inverse identity, and checks
each rational component by evaluation naturality on extended arrows.

`sectionEvaluation_fromIntrinsicSections` is the corresponding identity
for every ambient full domain `U` contained in `S`. The resulting element
is evaluation on its actual relative domain. The proof uses the same
full-domain recovery argument, now with `relativeMap` on every contained
ambient rational chart.

`fromIntrinsicSections_toIntrinsicSections` proves that returning a
pulled-back family gives the original ambient family. At each chart, the
preceding evaluation identity reduces the comparison to the extension of
its relative domain. A bounded identity map from this extension to the
original chart is an actual ambient inclusion: its structural equation is
the original inclusion's `comp_baseMap`, reversed. Evaluation naturality
and rational evaluation therefore give equality of the actual chart element.

`toIntrinsicSections_fromIntrinsicSections` proves the other inverse law.
The component now reduces to the relative representation of an extended
intrinsic rational chart. The bounded identity from the original chart to
this relative domain is an actual intrinsic inclusion because the chosen
ambient inclusion into `d` equals `extendInclusion`, by uniqueness of actual
inclusions. Evaluation naturality and rational evaluation finish the proof.
Neither inverse uses equality only at spectral points.

`subsetSectionsEquiv d hS` bundles the two constructed algebra homomorphisms
and these inverse laws. Its forward and inverse application lemmas identify
them exactly with `toIntrinsicSections` and `fromIntrinsicSections`.

## Restriction and structural maps

`toIntrinsicSections_restriction` and `fromIntrinsicSections_restriction`
prove naturality in every inclusion of ambient subsets (with the latter
subsets contained in `d.locus`). Their component formulas are definitionally
the same restrictions and evaluations.

`toIntrinsicSections_fromBase` sends the ambient structural family of `a : A`
to the intrinsic structural family of `d.baseMap a`. The extension retains
the composite bounded structural map, so full-domain base evaluation proves
the formula. `fromIntrinsicSections_fromBase` sends an intrinsic base family
of `a : d.algebra` to `toLocusSections d a` restricted to `S`; relative base
evaluation is precisely the original ambient bounded restriction from `d`.

## Provenance and scope

This is an internal consequence of `DomainOpenSections` and the actual
extension and relative constructions in `DomainLocalization` and
`DomainRelativeRepresentation`, imported through
`DomainOpenSectionsLocalization`. It evaluates the already constructed
compatible quotient families using the already proved full-domain recovery,
proves compatibility by actual-arrow naturality, and proves both inverses
with bounded identity arrows on unchanged algebras. No new original-literature
assertion, assumed analytic comparison or private peer draft is used.

The construction permits arbitrary positive radii, trivial valuations,
nonreduced or zero algebras and empty subsets or spectra. It compares the
actual algebras of compatible quotient families on subsets. Identification
with the previously constructed ordinary-open bounded-map pullback is a
separate obligation. It does not assert an ordinary inverse-image sheaf
comparison on a closed domain. Ordinary-open locally ringed-space restriction
comparisons, unrestricted atlases, analytic etale and quasi-etale sites,
equivariant sites and the Harris tower remain separate constructions.

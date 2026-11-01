# Actual domain presentations under locally refining subatlas selection

This module compares the actual bounded atlas presentations of a fixed
original-chart domain before and after deleting locally redundant original
charts. It connects the subset-preserving domain comparison in
`OriginalDomainRefinement` with the simultaneous full strong-map restriction
in `OriginalDomainStrongRestriction`.

Let `K` be a complete normed ultrametric field, let `A` be an actual
`AffinoidAtlasPresentation`, and let `P` select original chart indices.
The hypothesis `hP : A.atlas.IsLocallyRefiningSelection P` says that the
selected charts give finite relative local refinements inside every original
chart. For every `S : A.atlas.OriginalChartDomain`, the published order
isomorphism `A.atlas.originalDomainSubatlasOrderIso P hP` transports `S` to a
domain for the selected atlas without changing its literal underlying subset.
The new `coe_originalDomainSubatlasOrderIso` records that carrier equality.

## Chosen bounded comparison

`originalDomainSubatlasFunctor` first transports the domain along that order
isomorphism and then takes its actual contained-chart presentation for
`A.subpresentation P hP`. Its target is the category of chosen bounded atlas
maps, with the same independent universes for the field, spaces and chart
indices as `A`.

`originalDomainSubatlasMap S` maps this selected domain presentation to
`A.originalDomainPresentation S`. Its continuous map is the identity on
the actual subspace `S`. A source chart consists of a selected original
index whose range lies in `S`; its chosen target is precisely that original
index with the same containment proof. The pullback is the bounded identity
on the original presented affinoid algebra.

The monotonicity of this index assignment follows by passing between the
ambient and subspace range inclusions. Both chart commutativity and bounded
restriction compatibility are inherited literally. The application and
pullback lemmas record the identity formulas.

`originalDomainSubatlasMap_naturality` proves equality of the complete
chosen arrows for every inclusion `S ≤ T`. This yields the natural
transformation `originalDomainSubatlasComparison` from the transported
selected-domain functor to `A.originalDomainFunctor`.
`originalDomainSubatlasMap_inclusion` proves the ambient square: comparison
followed by the original domain inclusion equals selected domain inclusion
followed by `A.subatlasInclusion P hP`. Both equations use `Hom.ext` to compare
the continuous maps, chart-index assignments and entire bounded pullbacks.

## Full strong comparison

`strongSubatlasInclusion_mapsOriginalDomainCharts` supplies the chartwise
hypothesis needed for simultaneous domain restriction. Each selected original
chart contained in `S` maps into its identical original chart contained in
`S`; thus the needed target witnesses are constructed directly.

`originalDomainStrongSubatlasMap S` simultaneously restricts the published
full strong subatlas inclusion to the transported selected domain and to the
original domain `S`. It has the same underlying continuous identity as the
chosen comparison, as recorded by the application and base-map lemmas.

For every admissible source and target chart pair,
`originalDomainStrongSubatlasMap_pullback` identifies the entire pullback
with the original bounded atlas restriction. The admissibility witness is
converted from subspace range containment to the identical ambient range
containment by `restrictDomainsBaseMap_admissible_iff`.
At the chosen target copy of a source chart,
`originalDomainStrongSubatlasMap_pullback_selected` identifies that pullback
with the chosen comparison's bounded identity, using the original atlas
identity law. These equalities concern bounded algebra homomorphisms, including
their values on algebra elements; they do not infer equality from spectrum
points.

`isQuasiIso_originalDomainStrongSubatlasMap` proves that this full comparison
is a strong quasi-isomorphism. The ambient subatlas inclusion is already a
strong quasi-isomorphism. Its identity map carries the transported source
subset exactly onto `S`, by `Set.image_id`. The published simultaneous
restriction theorem therefore retains both the ambient homeomorphism and
every admissible local full affinoid-domain representation.

## Source and provenance

This is a derived compatibility construction from Berkovich, *Étale
cohomology for non-Archimedean analytic spaces* (1993), registered as
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are Definition 1.2.3 and Remark 1.2.4(i),
printed p.16 / PDF p.13, for actual atlas algebras and bounded restrictions;
Definition 1.2.7, printed p.18 / PDF p.15, for full strong morphisms;
Definition 1.2.9, printed p.19 / PDF p.16, for strong quasi-isomorphisms;
and Definition 1.3.1, printed p.23 / PDF p.20, for domains covered by
contained atlas charts. The natural transformation and the explicit domain
comparison here are derived from those definitions and the two imported
construction modules; no separately numbered original assertion is claimed.

## Scope

The comparison uses a locally refining selection of the same original
charts, retaining their original algebras, embeddings and restrictions.
No downward closure, directedness, greatest chart, reducedness, strictness or
nonemptiness hypothesis is imposed. The domain and site comparison being
connected here concerns fixed-original-chart domains. This module does not
construct an extended or saturated atlas, compare arbitrary unrelated atlas
algebras, or supply unrestricted composition or a category of full strong
maps. A full strong quasi-isomorphism is proved; a categorical isomorphism
of these chosen atlas presentations is not asserted.

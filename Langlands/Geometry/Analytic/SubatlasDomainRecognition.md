# Recognition of original local domains through a selected atlas

Author: Worker 36.

Every actual original local full domain is recognized by the local-domain
saturation of a locally refining selected atlas. This module constructs
the special cover, all intrinsic recognition conditions, and the bounded
equivalence between the original domain algebra and the resulting
recognized presentation. Its spectrum homeomorphism recovers the
unchanged original domain ambient map.

## Source and provenance

This is derived infrastructure for Berkovich, *Étale cohomology for
non-Archimedean analytic spaces* (1993), Proposition 1.2.13(i)–(ii),
printed p.21 / PDF p.18. Registered source:
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The original page was read for this construction; no source-specific
errata file was found in the available Library location.

The source compares completed domain families under passage to a subnet
and constructs the extended atlas's canonical bounded restrictions.
The present result treats an arbitrary old local full domain under the
explicit `IsLocallyRefiningSelection` hypothesis. It is an intermediate
construction toward that comparison, rather than the entire equivalent-net
assertion. No recognition output or bounded comparison is assumed.
The proof reuses the actual finite selected realization constructed in
`SubatlasDomainAffinoidRealization`, the pushout comparison route in
`RecognizedDomainSpecialCover`, and the generic finite-realization
recognition and chart-recovery theorems.

## Entire bounded overlap maps

Let `b = a.subatlas P hP`, let
`c : a.SelectedChartCover P parent`, and let
`U : Domain K (a.algebra parent)`. Write `d` for the constructed
`c.saturatedDomainGluing hP U`. Its components `E` and `F` are actual
full domains over the unchanged `U.algebra`.

`saturatedDomainOverlapEquiv` compares their actual intersection
pushout quotient with the presentation selected by `b.saturatedAtlas`
for the same literal overlap locus. It applies the existing actual
local-domain bounded equivalence to the extended overlap presentation.
It therefore retains the full quotient algebra data.

`saturatedDomainGluing_leftRestriction` proves that the stored atlas
restriction equals the actual left pushout map followed by this bounded
equivalence. The proof composes the overlap comparison inclusion with
the relative domain's extension inclusion. Uniqueness of actual
`b`-local-domain inclusions identifies that composite with the stored
saturated inclusion. Taking their bounded restrictions gives the
entire-map equality.

`saturatedDomainGluing_rightRestriction` proves the corresponding
right-map equality by the full universal property of `F`.
After precomposition with `F.baseMap`, the finite realization's
bounded compatibility identifies the stored map with the left
composite. The left-map equality and the actual pushout structural
equation identify it with the right pushout composite.
This is cancellation of a full represented-domain structural map,
not reconstruction from spectrum points.

`saturatedDomainGluing_overlapTensorMap` then identifies the genuine
completed-tensor map with the actual affinoid pushout quotient map
followed by the overlap equivalence. The proof uses completed-tensor
homomorphism uniqueness and checks both entire legs using the two
proved restriction formulas and the pushout tensor-leg equations.

## Specialness and intrinsic recognition

`saturatedDomainGluing_tensor_isAdmissibleEpi` proves admissibility
of this tensor map. The actual pushout quotient map is already an
admissible epimorphism. The overlap equivalence is an admissible
epimorphism because its bounded inverse is a bounded section.
Composition gives both surjectivity and the required positive uniform
quotient-norm bound.

`saturatedDomainGluing_isSpecialCover` pairs this result with the
Hausdorff topology on the union supplied by the constructed parent's
Banach spectrum homeomorphism. It needs no global Hausdorffness of
the ambient space.
`saturatedDomainSpecialSubset` packages the unchanged old domain
locus and the constructed finite special cover.

`saturatedDomainSpecialSubset_isRecognized` applies
`SpecialSubset.isRecognized_of_affinoidRealization` to this cover
and the constructed realization. That generic theorem constructs
intrinsic affinoidness of the unchanged canonical section algebra,
bijectivity of its canonical spectrum map, and full represented-domain
properties of its canonical component restrictions. The first condition
provides an actual finite positive-radius Tate presentation.
`saturatedDomainRecognizedSubset` packages these proved conditions;
its locus theorem is a definitional equality with the old domain locus.

`saturatedDomainAlgebraEquiv` composes the finite realization's
constructed equivalence with the canonical section algebra and the
recognized presentation equivalence. Its source is exactly the old
`U.algebra`.
`saturatedDomainRecognizedSubset_chart` uses the generic chart-recovery
theorem to show that the new chart is exactly the old ambient map
after the spectrum homeomorphism of this bounded equivalence.

## Every original local full domain

For `U : LocalDomain a`, `subatlasRecognizedLocalDomain` constructs
a finite selected cover of `U.index` using `a.selectedChartCover`
and applies the preceding construction to `U.domain`.
`subatlasRecognizedLocalDomain_locus` recovers `U.locus` literally.
`subatlasRecognizedLocalDomainEquiv` has source `U.algebra`, and
`subatlasRecognizedLocalDomain_chart` identifies its spectrum
homeomorphism with `U.ambientMap`. No finite cover or recognition
witness is supplied for these general declarations.

## Hypotheses and remaining scope

The coefficient field is a complete ultrametric normed field and may
have trivial valuation. The field, ambient space and original index
have independent universes. The ambient space has its given topology
and actual atlas; global Hausdorffness, reducedness, nonzero algebras
and nonempty covers are not added. Full-domain universal properties
retain all presented affinoid test algebras and finite positive polyradii.

This unit proves recognition of every original local full domain in
the selected local-domain saturation, including its actual algebra
and chart comparison. It does not yet compare arbitrary recognized
subsets of the two saturated atlases, prove naturality for all such
comparisons, or construct their category equivalence. Arbitrary
equivalent-net invariance, maximal-atlas uniqueness, unrestricted
analytic morphism identification, analytic etale and equivariant
sites, and Harris specialization remain subsequent obligations.

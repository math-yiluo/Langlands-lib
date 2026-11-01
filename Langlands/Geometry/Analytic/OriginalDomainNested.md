# Presentations of nested original-chart domains

This module compares the two actual atlas presentations of a domain inside an
original-chart domain. It retains the complete chosen bounded atlas arrows,
including their chart maps and algebra pullbacks.

## Source and provenance

The source context is Vladimir G. Berkovich, *Etale cohomology for
non-Archimedean analytic spaces* (1993), section 1.3, Definition 1.3.1, printed
page 23 / PDF page 20. There an analytic domain has the induced topology and
an atlas consisting of the affinoid domains contained in it, together with its
canonical inclusion. The induced-topology convention is also stated in
section 1.1, printed page 13 / PDF page 10. The registered source is
`berkovich-1993-etale-cohomology`, SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

The present result is derived for the restricted, published
`OriginalChartDomain` construction. For an actual presentation `A`, let `S`
be an original-chart domain of its atlas and let `U` be an original-chart
domain of the constructed atlas on `S`. The already published
`subspaceExtend` gives an ambient original-chart domain with carrier
`Subtype.val '' U.carrier`. We compare
`A.originalDomainPresentation (S.subspaceExtend U)` with
`(A.originalDomainPresentation S).originalDomainPresentation U`.
This is a construction with the original charts; no saturated atlas or
general analytic-domain descent result is assumed.

## Actual comparison

`subspaceExtendHomeomorph` inserts or forgets the intermediate membership in
`S`. Membership in the image supplies membership in `U`; injectivity of
subtype inclusion identifies the witnesses, as `mem_subspaceExtend_iff`
proves. Both maps are continuous by the induced subtype topology, and both
composites are the identity.

`subspaceExtendChartEquiv` identifies an original chart contained in the
ambient image with a pair consisting of that original chart contained in
`S` and its restricted range contained in `U`. The converse forgets the
intermediate containment. Its inverse laws retain exactly the original
index, with equality of containment proofs handled by proof irrelevance.

`originalDomainNestedMap` and `originalDomainNestedInverse` use these
continuous maps and index maps. Their index maps preserve chart containment:
the proof removes or inserts each of the two subtype restrictions using
the published chart-containment lemmas. Every chart algebra is literally
the same original algebra on both sides, and every pullback is its bounded
identity map. Thus chart commutativity and compatibility with bounded atlas
restrictions hold by reduction.

`originalDomainNestedIso` proves both inverse laws using `Hom.ext`, checking
the continuous map, the selected chart index and the entire dependent family
of bounded pullbacks. It does not infer equality of bounded algebra maps from
their induced maps on points. The two pullback lemmas state the retained
bounded identity maps explicitly.

## Compatibility and scope

`originalDomainNestedMap_inclusion` proves compatibility with the actual
chosen inclusion into the presentation on `S`.
`originalDomainNestedMap_ambientInclusion` proves compatibility with the
composite inclusion into `A`.
`originalDomainNestedMap_naturality` proves compatibility with every
inclusion `U ≤ V`, again by extensionality of complete chosen arrows.
`originalDomainNestedNatIso` bundles this as a natural isomorphism between
ambient-image realization and nested realization of subspace domains.

The coefficient, point and original chart index universes remain independent.
No nonemptiness hypothesis is imposed on either domain. This result concerns
the existing category of monotone chosen bounded atlas maps. It does not
construct general analytic morphism localization, structural sheaves,
equivalences of sheaf categories, or etale and equivariant sites.

# Supported derived comparison with an explicit higher-direct-image condition

This internal prerequisite supplies the ordinary/étale supported derived
comparison for the actual ordinary restriction, under explicit vanishing of its
higher direct images on the input sheaf. It does not establish that vanishing
for the smooth Godement terms.

The actual ordinary direct image is additive and left exact because it is a
right adjoint. The ordinary-open module sheaf category has enough injectives by
its existing sheafification and Grothendieck-category structure, transported
through a sufficiently small model. `etaleUnderlyingHigherDirectImage` is the
existing right-derived-functor construction applied to this actual direct
image. `underlyingTopologyCompactCohomology` applies the same construction to
the existing ordinary point-support compact-section functor.

For a Hausdorff analytic space with surjective field-point projection,
`etaleUnderlyingCompactCohomologyComparison` specializes the published
composite-functor comparison to ordinary direct image, ordinary compact
sections, and the proved degree-zero compact-section isomorphism. Its input
`hF` explicitly requires all positive right-derived ordinary direct images to
vanish on the given sheaf.

This condition makes the ordinary direct image of an étale injective resolution
a right resolution of the ordinary restriction. Ordinary direct image preserves
injectives by the proved flat site adjunction, so its resolution terms are
acyclic for ordinary compact sections. The published acyclic-resolution
comparison therefore makes the displayed supported comparison invertible.
`etaleUnderlyingCompactCohomologyIso` packages that actual map as an isomorphism.
`isZero_etaleCompactCohomology_of_ordinary_directImage_acyclic` transfers
ordinary compact vanishing through this isomorphism, retaining both the
higher-direct-image condition and the ordinary vanishing premise explicitly.

The proof uses existing Library and Mathlib constructions, with independent
field, space and coefficient universes. It uses neither analytic equivariant
comparison statement, nor restricted-injective acyclicity, nor an assumption
that equivariant restriction preserves injectives. The higher-direct-image
condition and ordinary compact acyclicity of the special Godement terms are
the further inputs that
`analyticEtaleGodementCompactAcyclic_of_correctedLocal_and_ordinary`, in
`Langlands.Cohomology.AnalyticEtaleSmoothPointProductLocalAcyclicCorrected`,
takes as hypotheses to reach `AnalyticEtaleGodementCompactAcyclicStatement`.

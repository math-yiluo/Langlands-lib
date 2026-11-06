# Finite rational ideal effectiveness and the full-domain reduction

`RationalIdealEffectivenessStatement` is an unproved proposition definition
restricting the published finite full-domain ideal-effectiveness target to
finite rational covers of the whole spectrum of a presented affinoid. It is
neither an axiom nor a proof of that restricted theorem.

`ofRationalCharts` constructs the concrete finite cover using the actual
rational quotient algebras and the original bounded structural maps.
Compatibility uses the actual `Domain.inter` restrictions between these full
domain representations. The global ideal is the same explicit intersection
of inverse images used in the published full-domain target.

The mathematical source for the effectiveness assertion is Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), Kiehl's Theorem
and Remark 1.2.1(ii), printed page 15 / PDF page 12. This is a derived ideal
specialization of the compatible finite-module descent theorem and its
section-equalizer identification. The registered source is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The source explicitly extends its assertions to general radii and trivial
coefficient valuations by the scalar-extension reduction cited there.

`idealEffectiveness_of_rationalIdealEffectiveness` proves a reduction to the
unchanged full-domain target. Given any finite full-domain cover of `U`, take
its published relative rational refinement over `U.algebra` and closedly
extend the local ideals through the chosen refinement restrictions. The
refinement module proves compatibility of this family and invariance of its
explicit contraction.

To apply the restricted theorem over `U.algebra`, test its two rational
intersection projections after extending their domains to the original
ambient affinoid. Extension retains their actual algebras and restriction
maps, so full-test compatibility gives exactly the required rational-cover
compatibility. The hypothesized rational effectiveness equations are then
the refined-cover equations, since the component algebras and maps are
unchanged. The proved refinement transport recovers effectiveness on the
original cover.

This reduction assumes the entire rational effectiveness theorem explicitly;
it does not supply the outstanding analytic descent step. Both propositions
retain arbitrary positive radii, trivial coefficient valuations, nonreduced
and zero algebras, empty spectra and empty finite covers.

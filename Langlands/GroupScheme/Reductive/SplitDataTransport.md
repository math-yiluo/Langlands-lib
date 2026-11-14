# Transport of actual split data through pullback comparisons

These internal lemmas support the proof of étale-local splitting by
retaining the actual coordinate data under the canonical comparison of
successive pullbacks. They are derived from the Library's pullback point
equivalence, its naturality, and its actual weight and root-datum
transport results.

`splitTorus.baseChangeIso_comp` proves coherence of the coordinate
split-torus comparison on every test scheme, using its global-unit point
model. `splitTorus.baseChangeHom_comp` combines that coherence with
naturality of the ambient pullback comparison.

`splitTorus.exponentWeightAmbientEquiv` identifies each actual exponent
weight module after an ambient group isomorphism. It uses the differential
of that isomorphism on the actual dual-number identity kernel, restricted
to the character weight module. `IsFibrewiseRootDatumOf.comp_ambientIso`
retains the same finite reduced coordinate datum and applies actual
root-datum transport on each field fibre.
`IsFibrewiseMaximalTorus.comp_ambientIso` similarly preserves maximality
on every residue-field fibre.

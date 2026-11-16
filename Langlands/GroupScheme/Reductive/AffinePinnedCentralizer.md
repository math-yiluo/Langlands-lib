# The actual canonical-cocharacter centralizer of a pinned model

This internal module identifies the dynamic centralizer of a supplied affine
pinned model's positive-coroot cocharacter with its actual coordinate torus.
The proof checks each residue-field fibre using regularity of the
positive-coroot sum and the field centralizer theorem, then applies the
published smooth centralizer recovery theorem. Because the residue-fibre
criterion is vacuous on an empty base, no nonemptiness or nonzero-ring
assumption is introduced.

Arbitrary base change transports this equality to every common test scheme.
The normalized torus inclusion therefore represents the cocharacter
centralizer. A comparison preserving the cocharacter transports one such
representative to the other, producing an actual torus isomorphism and its
inclusion square.

`cocharacterCentralizerIso` canonically identifies any supplied actual
centralizer representative with that coordinate torus. Its homomorphism
commutes with the two given inclusions.

These are derived consequences of the published regular-cocharacter and
residue-fibre results. They use the full actual coordinate tori and impose no
affineness or connectedness assumption on the common scheme. They do not prove
geometric local pinning normalization, its inner-class uniqueness, or the
comparison-existence target.

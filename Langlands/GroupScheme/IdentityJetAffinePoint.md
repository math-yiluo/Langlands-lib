# Actual affine test points of identity jets

For a relatively affine group `H` over `S`, the actual identity jet above every
affine base open `U` is affine. Its canonical chart from the spectrum of its
actual function ring, followed by the actual jet inclusion and an ambient map,
is an actual affine test point of the ambient group.

`affineJetPoint H F e b j hj n U` constructs that relative point for a supplied
ambient corepresentation `B` and an actual ambient scheme map `j` compatible
with the maps to `Spec R`. The coefficient algebra is the actual ring of jet
functions above `U`, with its `R`-algebra structure induced by the actual
composite jet projection to `Spec R`.

`affineJetPoint_left` records the precise scheme map. The theorem
`affineJetPoint_coordinates` proves that its classifying algebra homomorphism,
under the supplied affine-point equivalence, is exactly
`IdentityJet.jetCoordinateMap H j n U` on rings. The proof first shows that the
spectrum of the actual coordinate-function ring map is the same actual affine
chart map, using the global-sections/spectrum counit and the affine-open chart
naturality law. Full faithfulness of relative spectrum then identifies the
classifying maps.

The general helper `spec_coordinateMap` states this scheme-function identity
for any affine open in any scheme mapped into a spectrum. These are internal
consequences of existing affine-open, relative-spectrum, and actual jet APIs.
No smoothness, flatness, or finite-presentation assumption is needed. The
module does not yet assert the conjugation-orbit or classified-kernel equality.

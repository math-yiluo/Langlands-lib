# Canonical affine direct-image comparison

This internal derived helper identifies the actual sheaf base-change map over a
morphism of spectra with the tilde of the specified scalar sections comparison,
using the canonical tilde counits. It does not assume that the total spaces are
affine or that their commuting square is Cartesian.

The construction `affineDirectImageTildeMap` applies tilde to
`scalarSectionsBaseChangeMap` and then the target tilde counit. The theorem
`pullback_fromTildeΓ_comp_pushforwardBaseChange` compares this construction with
the published `pushforwardBaseChange` after the source tilde counit. Its proof
uses the tilde-pullback adjunction and checks canonical global generators: the
pushforward square isomorphism acts as the identity on top sections, and both
maps send a generator to the actual pullback unit on sections.

Consequently, if both direct-image sheaves over the spectra are quasi-coherent
and the actual scalar sections map is invertible, the specified sheaf comparison
is invertible. Quasi-coherence is an explicit hypothesis of this helper; this
file does not prove quasi-coherence of direct images or local freeness.

The provenance is the formal adjunction construction in the imported Library
modules `DerivedRestriction`, `CohomologyBaseChangeZero`, and `TildePullback`;
no new source theorem or geometric hypothesis is asserted.

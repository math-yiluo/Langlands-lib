# Actual subgroup jets and ambient coordinates

For an affine group scheme `G` over `Spec R`, a base change `S → Spec R`
and an actual group homomorphism `H → G_S`, `ambientProjection` is the
actual map from `H` to the fixed affine coordinate spectrum of `G`.

The identity section of a corepresented group is the spectrum of the
algebraic counit: both represent the identity algebra point. Preservation
of identity by actual group homomorphisms, and its compatibility with
base change, then identify the composite identity-to-ambient-coordinate
map. Pullback of functions shows that the ambient augmentation ideal
vanishes on the actual identity of `H`.

If `H → S` is affine, `ambientQuotientCoordinates` applies
`IdentityJet.quotientCoordinates` to these actual maps. It supplies global
sections of the actual order-`n` identity jet from the fixed ambient
augmentation quotient. No closedness of the homomorphism, smoothness,
affineness of the base, or rank condition is required.

This is an internal functorial comparison derived from the affine
corepresentation, identity preservation, base change, and the proved
global jet coordinate construction.

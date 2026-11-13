# Actual type C index coordinates from a prescribed block torus

This internal adapter starts with an actual semisimple group, a supplied maximal
split torus, and an isomorphism over the separable closure that sends that torus
to the repeated-block torus of the split symplectic group. It constructs actual
Tits index data with the corresponding integer restriction coordinates.
`typeCBlockTorusCoordinates` supplies the additive equivalence used for these
coordinates by composing character base change, the canonical torus isomorphism,
and the integer coordinates over the separable closure.

The proof aligns a ground-field maximal torus with the diagonal torus and
transports the coordinate pinning. Character coordinates are composed through
base change and the canonical split-torus identification. The block-character
calculation gives the simple restrictions. Perfectness of the standard split
torus's character/cocharacter pairing realizes the decreasing positive integer
functional by an actual cocharacter. Zero-or-positive simple restrictions then
give the required compatible actual index. The transported simple-root indices
preserve the Cartan pairings and the computed coordinates.

The provenance is the Library's actual torus alignment, pinning transport,
coordinate root datum, block restriction calculation, and elementary positivity
helper. No classification of forms or distinguished vertices is assumed here;
the supplied maximal torus and block-image square remain hypotheses.

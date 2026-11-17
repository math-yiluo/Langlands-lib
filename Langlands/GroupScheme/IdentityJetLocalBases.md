# Finite local bases of the actual identity jet module

For an actual group scheme `G` over any base scheme `S`, the previously
constructed identity jet inclusion is a closed immersion. If the structure
morphism of `G` is affine, its composite with that inclusion, the jet
projection, is affine. The instance `isQuasicoherent_module` applies affine
pushforward of quasi-coherent modules to the actual structure module of the
jet subscheme. Thus `IdentityJet.module G n` is quasi-coherent for every
order `n`, without a smoothness assumption.

Assume also that the structure morphism of `G` is smooth.
`hasFiniteLocalBasis G n` combines quasi-coherence with the finite projective
section modules on every affine open proved in `IdentityJetSheaf`. The included
general affine-section criterion spreads local module bases to actual finite
free sheaf charts and assembles them into finite local basis data. This proves
finite local freeness over an arbitrary base, with ranks allowed to vary.

`finiteLocalFrames G n` chooses actual finite frames only from that proved
existence. `determinant G n` is the existing finite locally free determinant
construction applied to the actual jet module and its proved finite local
bases. Its gluing uses the actual determinants of frame transitions.

This is an internal supporting construction, derived from the actual jet
subscheme and pushforward, the affine section comparison, and the general
finite projective affine-section criterion. It does not yet identify higher
augmentation layers with symmetric powers, compare this determinant with the
dual Lie determinant, or assert ampleness.

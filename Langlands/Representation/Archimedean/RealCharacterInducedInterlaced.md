# Interlaced integral character-induced swaps

This module exposes a linear equivalence between the actual `O(3)`-finite standard-module
function spaces of `[character c, induced d]` and `[induced d, character c]` when
`d.exponent - |d.weight| / 2 - c.exponent = -m` for an integer `0 < m < |d.weight|`.
It has no landing, uncertainty, irreducibility or classification hypothesis.

The implementation adapts the two tail constructions in
`RealCharacterInducedSwap` and retains their actual bijections. In the odd parity
case it constructs a bijection in the reverse direction and inverts it; in the even parity
case it uses the forward bijection directly. Each composite consists of a tail multiplier
and a generic multiplier along the two adjacent block rotations. The generic factor is
injective because its possible zeros have the wrong parity. On the kernel of the tail
factor, modes along that axis lie below its threshold, while the induction block forces
modes along the other axis above `|d.weight|`. The proved two-axis uncertainty theorem makes
the function zero. The proved compact degree-layer comparison upgrades injection to
surjection. The proved landing statements ensure the composite satisfies the target's
Fourier conditions.

`exists_bijective_tail_first` and `exists_bijective_tail_second` discharge landing with
`RealSwapLandingIntegral.inducedFirst` and its proved mirror, and discharge uncertainty
with `RealOrthogonalUncertainty.realOrthogonalBlockUncertainty`. The result
`exists_bijective_interlaced` merges the parity cases and converts exact intertwining
modulo the zero subspace to `IsRealStandardIntertwiner`.

`interlacedEquiv` chooses that bijective linear map and packages it as a linear equivalence;
`interlacedEquiv_isIntertwiner` proves its compact and Lie equivariance, and
`injective_interlaced` supplies `RealInjectiveIntertwinerExists` in the character-first
direction. No real-exponent ordering is needed in this integral range. The module does not
assert the full unlinked swap outside this range.

Provenance is internal and derived. The tail-case proofs are adapted from the
construction in `RealCharacterInducedSwap`. No external literature result is used.

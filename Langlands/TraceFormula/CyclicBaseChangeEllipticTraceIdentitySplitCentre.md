# Reduction of the elliptic trace identity to the split-centre quotients

`CyclicBaseChangeEllipticTraceIdentityOnSplitCentre` is the elliptic twisted trace identity
for number fields in a common universe and for cuspidal operator realizations trivial on
their positive split centres. It keeps the two finite places with a single place above
them, supercuspidality at both upper places, weak base change, and irreducibility and
admissibility of the given lower local component. The two representation universes are
independent.

`CyclicBaseChangeEllipticTraceIdentitySplitCentreReductionStatement` asserts that this
version implies `CyclicBaseChangeEllipticTraceIdentityStatement` for number fields in
a common universe. The theorem `cyclicBaseChangeEllipticTraceIdentity_of_splitCentre`
proves the implication.

## Proof

`CuspidalOperatorRealization.weakBaseChangeSplitCentre` supplies a Hecke character `χ`
given by a complex power of the lower idelic norm. Twisting by `χ ∘ det` downstairs and by its norm
pullback composed with the determinant upstairs makes both realizations trivial on
their positive split centres and preserves weak base change. Determinant twists
preserve supercuspidality at the two upper places and preserve irreducibility and
admissibility of the lower component. Apply the split-centre version to the twisted
spectral presentations.

At the first place, the completed tensor product is identified with the product of
local completions by `completedTensorComparison`. There is only one factor, so the
product formula `norm_pi` identifies its norm with the single local norm. The
component of the tensor comparison induces a continuous map on general linear
groups by the universal property of the module topology. Consequently
`HeckeCharacter.normComp_finiteComponent` identifies the upper local twist on the
tensor algebra with the determinant norm pullback of the lower one. Both local
characters have open kernel by local constancy of finite Hecke characters and
continuity of the component map.

`CyclicBaseChangeEllipticConclusion.of_heckeDeterminantTwist` uses the equivalences
between the actual twisted components and the twists of the original components.
It then applies `HasEllipticTraceIdentity.of_equiv` and
`HasEllipticTraceIdentity.of_determinantNormTwist` to obtain the identity for the
original pair. The latter multiplies the test functions by inverse character
weights and reuses the nonzero scalar of the twisted identity.

The reduction is derived from `CyclicBaseChangeEllipticTraceIdentityStatement`,
the compatible split-centre normalization, and the local determinant untwisting
identity. Its conclusion uses the same test functions, measures and support
conditions as the elliptic trace identity.

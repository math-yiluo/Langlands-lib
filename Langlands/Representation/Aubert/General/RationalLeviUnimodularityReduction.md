# General reductive unimodularity on the literal standard Levi

This internal reduction uses the published all-test standard Levi
representative and its canonical multiplicative point homeomorphism.
It does not prove general reductive unimodularity or dynamic-centralizer
reductivity. Both proposition inputs remain explicit.

`modularCharacter_continuousMulEquiv` proves that a continuous multiplicative
equivalence preserves Mathlib's modular character, for two locally compact
topological groups in independent universes. Push a Haar measure on the source
forward to the target. Right translation on the target intertwines with right
translation on the source, whose pushforward scales by the source modular
character. The Haar scalar-factor formula for the target then gives the same
value. No countability, Hausdorffness or nonarchimedean assumption is used in
this generic transport.

`standardLeviScheme_isConnectedReductive` uses the supplied
`StandardCocharacterStatement` to realize the actual standard Levi functor as
the dynamic centralizer of a standard cocharacter. Its existing closed
representative is `Standard.leviScheme`, with map `Standard.leviHom`. Apply the
explicit `DynamicCentralizerReductiveStatement` to that same representative.
No new representative or rational-point carrier is chosen.

`standardLevi_modularCharacter_eq_one` assumes the general
`RationalReductiveUnimodularityStatement`, the dynamic-centralizer statement,
and the usual connected-reductive, maximal-split-torus and generic-cocharacter
data. It uses the already published `leviRationalPointHomeomorph` to transfer
local compactness, Hausdorffness and the nonarchimedean group structure to the
canonical point topology of `Standard.leviScheme`. Local compactness of the
literal Levi is explicit in this helper; the parabolic application obtains it
from the closed-projection equalizer. Apply general reductive unimodularity to
the representative and transfer its modular character through the same
homeomorphism.

`rationalParabolicModulus_of_reductiveUnimodularity` concludes the exact
published `RationalParabolicModulusStatement`, conditional on the general
reductive-unimodularity and dynamic-centralizer-reductivity propositions.
At each original input it obtains local compactness of the literal Levi
from the continuous-projection closed equalizer, applies the preceding Levi
transport, and invokes `standardParabolic_modularCharacter_of_levi`.
The ambient conclusion is the same general unimodularity input applied to
`G` itself. No other premise is added.

The provenance is internal: this is a consequence of the stated structural
inputs, the published standard representability and point topology results,
and Mathlib's Haar pushforward and scalar-factor identities. It supplies the
intrinsic literal-Levi hypothesis of `standardParabolic_modularCharacter_of_levi`;
it supplies no unconditional proof of `RationalParabolicModulusStatement`.

# Twisting commutes with pullback

`TwistPullbackCompatibility` states that restriction of `twist chi rho`
along any group homomorphism `phi : H →* G` equals the twist of the
restricted representation by `chi.comp phi`.

The hypotheses are groups `G, H`, a commutative ring `R`, an `R`-module `V`,
an arbitrary representation `rho`, and an arbitrary unit-valued homomorphism
`chi`. No continuity or injectivity of `phi` is assumed.

This is an internal definitional compatibility of the scalar-twist formula.
Henniart's composed quasicharacters in Section 1.2(2), printed page 440,
motivate the interface: literature ID `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
No determinant or reciprocity map is constructed here.

Exact accepted and published definition dependency:
`c83db975-8b79-4fbb-9901-2db836910a0a`, version 1, Lean source SHA-256
`9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`,
at public commit `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`, with the same
checked source bytes. Environment:
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The Lean declaration is a proposition definition.

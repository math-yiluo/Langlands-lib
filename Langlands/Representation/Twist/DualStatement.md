# Character twisting and the algebraic dual

`TwistDualCompatibility` says that the algebraic dual of `twist chi rho`
equals `twist chi⁻¹ rho.dual`. All representations in the equality act on
`Module.Dual R V`. The hypotheses are exactly a group `G`, a commutative ring
`R`, an `R`-module `V`, and a unit-valued homomorphism `chi`.

Mathlib's `Representation.dual` uses
`(rho.dual g f)(v) = f(rho(g⁻¹)(v))`. Therefore the scalar in the dual twist is
`chi(g⁻¹) = chi(g)⁻¹`, which fixes the inverse convention unambiguously.

This is an internal algebraic compatibility, motivated by Henniart 2000,
Section 1.2(2)-(3), printed page 440; literature ID
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
It concerns the full algebraic dual. It does not assert that this dual is
smooth or identify it with the smooth contragredient used for p-adic groups.

Exact accepted and published dependency: twist definition artifact
`c83db975-8b79-4fbb-9901-2db836910a0a`, version 1, Lean source SHA-256
`9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
The public commit is `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`, with the
same checked source bytes. Environment:
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The declaration defines a proposition, rather than assuming or proving it.

# Algebraic laws for character twisting

`Langlands.TwistAlgebraLaws` states, for every group `G`, commutative ring `R`,
`R`-module `V`, representation `rho`, and characters `chi, eta : G →* Rˣ`:

1. The trivial character leaves the representation unchanged.
2. Twisting first by `eta`, then by `chi`, equals twisting by `chi * eta`.
3. Twisting by `chi`, then by its pointwise inverse, returns `rho`.
4. Twisting by the pointwise inverse, then by `chi`, returns `rho`.

These are equalities on the original underlying module. Products and inverses
are in the commutative group of unit-valued homomorphisms.

This is an internal algebraic consequence of `Langlands.twist`, not an additional
result attributed to the literature. The convention and source correspondence
are documented in `Twist/Definitions.md`: Henniart 2000, Section 1.2(2),
printed page 440, source ID `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

Accepted and published definition dependency:
`c83db975-8b79-4fbb-9901-2db836910a0a`, version 1, public commit
`3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
Its exact Lean source SHA-256 is
`9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
The publication preserves the exact checked source bytes. The extra Mathlib
import `Mathlib.Algebra.Group.Hom.Instances` supplies the group structure on
the space of characters. Environment:
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

The Lean declaration is a proposition definition, not a proof or an assumption.

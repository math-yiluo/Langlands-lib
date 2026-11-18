# Nilpotent rigidity of local quasi-isogenies

Rapoport–Zink, *Period Spaces for p-divisible Groups* (1996),
§2, printed p. 52 (PDF page 67), equation (2.1) and its surrounding
paragraph, state the bijectivity of restriction of quasi-isogenies to a
nilpotent closed subscheme of a scheme on which `p` is locally nilpotent.

`LocalQuasiIsogenyNilpotentRigidityStatement` is the case of two globally
coordinated formal module laws on an affine base, with their restrictions
to any open of its spectrum. It takes a prime `p`, a commutative ring `R`,
and a nilpotent ideal `I`. Both formal laws are `p`-divisible in the
Library's sense, which includes nilpotence of `p` in `R`, affine fppf
lifting for `[p]`, and represented finite locally free scalar-power
kernels. The scalar ring is `ℤ` and the rational Hom is formed over
`ℚ`, placed in the universe of `R`.

The source of the map is the type of actual local quasi-isogenies on the
chosen open. The target consists of the same kind of sections between
the actual quotient-coefficient formal laws over the inverse-image open
of `Spec (R/I)`. The map is `LocalQuasiIsogeny.baseChange` along the
canonical quotient algebra homomorphism. The proposition asserts a unique
lift of each such section through this map by asserting its bijectivity.

This file defines the proof target for this affine formal-module case of
the rigidity theorem.

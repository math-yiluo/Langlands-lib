# Haar measure under reflected inverse transpose

This internal prerequisite treats the actual upper-unipotent group and the
published map `Whittaker.reflectedUnipotent u = w (u⁻¹)ᵀ w`, with the unsigned
long Weyl element `w`. It does not establish a matrix-to-rank-one functional
equation.

`measurePreserving_involutive_automorphism` proves that an involutive continuous
group automorphism preserves every regular Haar measure on a locally compact
group. Mathlib's positive Haar character is multiplicative under composition.
The involution therefore gives a positive character value whose square is one,
so the value is one. The Haar scaling formula then gives the exact pushforward
identity.

`reflectedUnipotent_involutive` checks the involution in the actual matrix unit
group, using the published involutivity of inverse transpose and `w² = 1`.
`reflectedUnipotentEquiv` packages the same map as a continuous group
automorphism. The multiplication formula follows by cancelling the middle
copies of `w`; continuity follows from continuous inverse transpose and group
multiplication.

`measurePreserving_reflectedUnipotent` applies the general result to any regular
Haar measure on this upper-unipotent group. It introduces no scalar and imposes
no normalization or additive-character condition. The construction allows
every natural `n`, including `n = 0`, and any commutative topological ring for
which the group has the displayed local compactness and measurable structures.

All content is derived internally from the published actual matrix maps and
Mathlib's Haar modulus. The character reversal of this same map is already
proved in `Whittaker.DualTransform`.

`inverseTranspose_reflected_mul_weyl` proves the unsigned group identity
`iota(reflectedUnipotent u) * w = w * u`, where `iota` is inverse transpose.
This is an equality in the actual matrix unit group, obtained from `w² = 1`.

`measurePreserving_reflectedUnipotent_prod` preserves the product with any
second supplied S-finite measure, fixing that variable; the unipotent measure
is also assumed S-finite for Mathlib's product transport theorem.
`measurePreserving_reflectedUnipotent_unipotentHaar` specializes to the actual
integral-subgroup-normalized measure over every nonarchimedean local field.
Its proof obtains local compactness from the actual closed unipotent subgroup
and finite-dimensional matrix topology. Both specializations retain the exact
measure and introduce no normalization condition.

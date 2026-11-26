# Regularity under unramified character twists

For an open-kernel complex unit-valued character `ψ`, `characterMultiplyTest`
is multiplication of a test function by `ψ`. It uses the Library's
`Distribution.multiplyTest` and the local constancy of `ψ`.
`characterTwistDistribution` pulls distributions back along this linear map.

Unramified characters are trivial on compact subgroups. This condition
is preserved by products, inverses and pullback along continuous group
homomorphisms. On a Hausdorff, locally compact, totally disconnected group,
a compact open subgroup lies in the kernel of every unramified character,
so such a character has open kernel.

`twistedDistribution_twist_eq_comp` compares the actual twisted distribution
of `twist ψ ρ` with pullback of the distribution of `ρ`. The integrated
operators match by the pointwise equality of the weighted orbit maps, after
which one composes with the original linear operator `A` and takes the
finite-rank trace. The formula takes any admissibility witness for the twist
and any linear endomorphism `A` of the carrier.

`exists_regular_characterTwistDistribution` proves that for a fixed `d` and
`φ`, evaluating the pullback of `d` at `φ` is a finite complex linear
combination of evaluations of the unramified character. Use the Library's
`Hecke.RenardTestDecomposition.doubleCosetExpansion` to express `φ` as a
linear combination of indicators of distinct double cosets of a compact
open subgroup `K`. On `K g K` the character takes the constant value
`ψ(g)`. Each coefficient is therefore the evaluation of `d` on one indicator
multiplied by that indicator's coefficient in `φ`.
`exists_regular_twistedDistribution_twist` specializes the result to a
fixed twisted distribution using the pullback formula.

This is the regularity of fixed-test evaluation used for the unramified
orbit in the pseudo-coefficient construction of Henniart–Lemaire (2011),
II.5.13, pp. 113–114.

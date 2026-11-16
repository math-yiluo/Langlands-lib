# Extracting the centralizer factor of a big-cell relation

This internal construction extracts the zero-weight part of a cell relation.
It combines the all-test root-product limits of `SimpleWallCellFactors`
with the published dynamic opposite-intersection and uniqueness theorems.
It requires no field or reducedness assumption.

The generic theorem `Dynamic.centralizer_factor_eq_of_triple_eq` works in
an affine group scheme over the spectrum of any commutative ring. On every
relative test scheme, it considers equal products `m * (z * v)`, where `m`
is contracted by the opposite cocharacter, `z` centralizes the cocharacter,
and `v` is contracted by the original cocharacter. It proves equality of
the two centralizer factors.

The ratio of the two opposite factors lies both in the opposite dynamic
unipotent subgroup and in the original dynamic parabolic. The published
all-test opposite-intersection theorem makes that ratio the identity.
Cancelling the equal opposite factors leaves equal centralizer/unipotent
products. Their dynamic limits are the respective centralizer factors;
uniqueness of limits in the affine, hence separated, ambient group proves
the result. No smoothness or reductivity is used.

`centralizer_factor_mul_of_triple_relation` allows right multiplication by
another centralizer point. The centralizer normalizes the dynamic
unipotent subgroup. Moving the right multiplier across the positive
contracted factor and applying the previous theorem proves the precise
right-multiplication relation between the centralizer factors.

The coordinate helpers identify negation of an exponent vector with
inversion of the cocharacter parameter and show that the zero-weight part
of a root product is unchanged by this negation.

For a cell point `x`, `cellLeviPart` keeps the zero-weight root products on
each side of the original torus coordinate. `cellWallNegativePart` is the
original negative root product times the inverse of its zero-weight part;
`cellWallPositivePart` is the inverse zero-weight part times the original
positive product. Multiplication of these three defined factors recovers
the original cell point exactly.

Given actual root parametrizations, the middle part centralizes the
cocharacter: both zero-weight root products do, and the torus coordinate
commutes with every coordinate cocharacter. If the enumerated negative
factors have nonpositive weights and the positive factors nonnegative
weights, the outside factors lie in the opposite and original dynamic
unipotent subgroups, respectively, by the preceding root-product results.

`cellLeviPart_mul_of_cell_relation` applies the generic comparison to any
right-translation relation between full cell points, when the translating
point centralizes the chosen cocharacter. It gives the exact induced
relation between their middle parts on every test scheme. Besides actual
root parametrizations and these weight signs, only affineness of the
ambient group is required; no source-cell open immersion is needed for
this extraction.

The module does not yet specialize the middle part to the two individual
roots of a simple wall or prove the coroot quotient's negative-simple
translation law.

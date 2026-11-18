# Cartan-cell height bounds retaining central valuation coordinates

This module is an internal extension of the published norm-kernel Cartan-cell
argument in `RationalCartanCellHeight`. It reuses its finite torus-height bound
and the rational spanning theorem for simple roots and restricted rational
characters, while bounding the rational-character valuations of an arbitrary
group point by the existing `rationalValuationCoordinates`. No new assertion
is attributed to original literature. All declarations are in
`Langlands.HarishChandraSchwartz`.

`exists_norm_pi_int_hom_le` proves that any additive homomorphism from a finite
integer coordinate lattice to the integers has a uniform linear norm bound.
It expands the input in the standard coordinate basis, applies the triangle
inequality, and bounds each coordinate norm by the supremum norm of the input.
The constant is the sum of the norms of the images of the standard basis
vectors, including the empty sum in dimension zero.

`rationalValuationCoordinateEvaluation hG chi` expresses evaluation at one
rational character as an additive functional on the existing valuation image
coordinates: invert `rationalValuationLatticeEquiv` and evaluate the actual
integer valuation at `chi`. Its application to `rationalValuationCoordinates`
is exactly the original rational-character valuation, as proved by
`rationalValuationCoordinateEvaluation_apply`.
`exists_abs_rationalCharacterValuation_le_coordinates` applies the preceding
finite lattice bound to obtain a nonnegative constant for each character,
uniform over every group point.

For an arbitrary nonarchimedean local field, connected reductive group with
maximal split torus and generic cocharacter, compact subgroup `K0`, finite set
`F0` of actual centralizer points and arbitrary finite matrix representation
`rho`, `exists_rationalHeight_le_cartanCell_coordinates` gives one nonnegative
constant `C` such that

`rationalHeight rho g <= C * (1 + T + norm (rationalValuationCoordinates g))`

whenever `T >= 0`, all absolute simple-root pairings of the cocharacter `y`
are at most `T`, and `g` belongs to the actual Cartan cell
`union f in F0, K0 * uniformizerPowers(y) * f * K0`.
There is no norm-kernel restriction on `g`, no chamber positivity assumption
on `y`, and no closed-immersion assumption on the matrix representation.
Neither existence of a Cartan cover nor an Iwasawa decomposition is assumed
or proved by this height comparison.

The proof first bounds matrix height on the compact factors and finite set.
Compact factors lie in the rational norm kernel. Consequently the valuation
of each rational character on `g` is its pairing with `y` plus its value on
the finite factor. The evaluation-functional bound controls the former by a
constant times `1 + T + norm (rationalValuationCoordinates g)` after the finite
factor is removed by the triangle inequality. Bounds for simple roots and
restricted rational characters propagate to every torus character using the
published rational spanning theorem. The published finite torus-height bound
then controls the uniformizer factor. Subadditivity combines all factors with
one nonnegative constant, chosen before `y`, `T` and `g`.

`exists_one_add_height_le_coordinates_on_bounded_cells` fixes any `T >= 0`
and obtains `D >= 1` with

`1 + rationalHeight rho g <= D * (1 + norm (rationalValuationCoordinates g))`

uniformly over all such bounded-root Cartan cells. If `C` is the preceding
constant, the proof takes `D = 1 + C * (1 + T)` and uses nonnegativity of
`T` and the coordinate norm. This is the height comparison needed to use
central Fourier decay on the bounded-root part of the wave-packet argument.
It asserts no packet bound outside those regions and does not prove full
Schwartz membership or synthesis continuity.

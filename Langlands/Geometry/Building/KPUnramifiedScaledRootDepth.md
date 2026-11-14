# Scaled upper root depth factors of a concrete unramified lift

This internal derived unit defines `ApartmentLift.scaledRootDepth y a r` as
the existing multiplier-scaled upper subgroup for the base change of the lower
character `a`, using the valuation at the supplied lifted point `L.e y`.
The base field is a nonarchimedean local field, the ambient group is affine,
and the parahoric building data and special-torus apartment lift are supplied.
The definition allows every lower character and every real depth.

`rationalConjugate_mem_scaledRootDepth` and its `iff` version prove stability
under every automorphism of the maximal unramified extension over the base
field. The proof maps the generator supremum under coefficient conjugation.
Galois transport preserves actual upper roots and restriction multipliers,
because character pullback commutes with transport and base-changed lower
characters are fixed. The transported upper filtration is the original one
because the lift's root-function family is fixed. Applying the same argument
to the inverse automorphism gives the reverse implication.

For an actual lower root and nonnegative real depth `r`,
`scaledRootDepth_inf_double` identifies the intersection of the scaled factors
for `a` and `2a`, both at depth `r`, with the scaled factor for `2a` at depth
`2r`. This specializes `torusRestrictedRootDepthSubgroup_inf_double`;
base-change root reflection supplies the nonzero upper lower-torus character.
Smoothness is supplied by the connected reductive ambient group in the
parahoric building data; splitness and opposite factor pairs come from the
comparison torus and lift.

`rootFiltrationSpan_eq_scaledRootDepth_sup` proves that the uniform upper
positive restriction fibre at nonnegative real depth `r` equals the join of
`scaledRootDepth y a r` and `scaledRootDepth y (2 • a.val) r`, for every actual
lower root `a`. The proof identifies the concrete fibre-indexed supremum with
`torusUniformRootDepthSubgroup` and applies
`torusUniformRootDepthSubgroup_eq_block`. The needed relative root system is
supplied by `relativeRootSystem` for the connected reductive group and the
maximal split torus already present in the parahoric data.
`fieldFactorization` supplies the compatible scalar-extended torus inclusion.
Character base change preserves doubling, so the resulting block is exactly
the displayed join.

`mem_scaledRootDepth_sup_iff_exists_mul` gives a set-product description of
that join at every real depth, without a nonnegativity assumption: an upper
point `g` belongs to it exactly when `g = x * z`, with `x` in the scaled
`a` subgroup and `z` in the scaled `2a` subgroup, both at the same depth `r`.
The proof applies
`mem_torusRestrictedRootDepthBlock_iff_exists_mul_of_noHigherRoots`.
Its nonzero-character hypothesis follows from root reflection under field
base change. For its higher-root exclusion, the private helper reflects any
putative root `n • a` upstairs to the lower field and contradicts
`HasRelativeRootSystem.nsmul_not_mem_of_three_le` when `3 ≤ n`.
The generic product theorem supplies the required commutation of these
actual root-depth factors; no factorization premise is added to the lift.

At nonnegative real depth,
`mem_rootFiltrationSpan_iff_exists_scaled_mul` combines the join equality
and this product description. The companion
`mem_rootFiltrationSpan_iff_exists_double_scaled_mul` allows the doubled
factor first: factor `g⁻¹` in the preceding order and invert both factors.
For the converse, subgroup closure puts either ordered product in the join,
which equals the uniform upper span.

This is a composition of published character transport, root transport and
root-depth constructions with the companion uniform-block helpers. It makes
no direct original-literature claim and proves no rational factor descent or
smooth integral-model existence. The products are over the unramified
extension field. They do not assert that either factor is rational over the
lower field and do not establish the complete root-comparison statement.

# Polynomial growth of the scalar extension factor on the real opposite cell

`RealOppositeScalarGrowthStatement`: for every rank `r + 1` and every exponent vector
`s : Fin (r + 1) → ℂ` there are `C ≥ 0` and `M` such that

`‖oppositeScalar s z‖ ≤ C (1 + ‖z‖)^M`

for all upper-entry coordinate vectors `z` (supremum norm), where `oppositeScalar s` is the
scalar factor of the upper-Borel extension on the opposite cell (`RealOppositeCompactChart`).
`realOppositeScalarGrowth` proves it.

## Proof

Write `s` as the shifted position exponents of the character list `characterList 0 s'` with
trivial signs (`shiftedExponent_scalar`). The constant compact profile `1` has trivial sign
parity, so its extension `f = extension s 1` lies in the principal series of that list
(`scalar_mem`, via `gramFunction_mem_principalSeries`), and it has norm at most one on the
orthogonal group. On the opposite cell `f(oppositePoint z) = oppositeScalar s z`
(`extension_oppositePoint`). The Library's height bound `realPrincipalSeriesHeight` bounds
`|f(g)|` by `A · height(g)^N₀`, and `realMatrixHeight_transpose_le` (module
`RealOppositeMoment`) bounds the height of `oppositePoint z = uᵀ` by a power of
`1 + ‖z‖`, because the entries of `u` are bounded by `1 + ‖u - 1‖ = 1 + ‖z‖`
(`norm_upperEntries`).

This is the real counterpart of the Library's `ComplexOppositeScalarGrowth`; it controls
the scalar factor in the approximation of compact profiles in
`RealWhittakerApproximateIdentity`.

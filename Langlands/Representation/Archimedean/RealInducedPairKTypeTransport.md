# Compact transport for two real induction blocks

This is a derived helper for the two-induced-block filtration problem. It uses
the concrete standard modules and published compact transport and counting
theorems. No exponent inequality or restriction on the two integer weights is
assumed.

Write `S(d,e)` for the `O(4)`-finite functions of
`realStandardModule 4 [RealBlock.induced d, RealBlock.induced e]`.
The map `RealInducedPairKTypeTransport.swapMap d e` is a complex-linear
bijection from `S(d,e)` to `S(e,d)` commuting with right translation by
`O(4)`. The theorem `surjective_of_injective` states that every injective
complex-linear map in that direction commuting with right translation by
`O(4)` is surjective. Interchanging `d` and `e` supplies the other direction.

These results concern the compact-group action. They do not construct an
intertwiner for the Lie algebra, a four-crossing exchange operator, or a
filtration, and do not prove the unconditional filtration statement
`RealInducedInducedFiltrationStatement`.

The matrix `swapMatrix` sends `e₀` to `e₂`, `e₁` to `e₃`, `e₂` to `e₀`
and `e₃` to `e₁`. Entrywise computation proves that it is orthogonal and
that its element `swap` of `O(4)` squares to the identity. It carries the
ordered rotation plane `(0,1)` to `(2,3)` with the same orientation and
conversely: `swap r₀(θ) = r₂(θ) swap` and
`swap r₂(θ) = r₀(θ) swap`.

On `O(4)`, `swapMap d e f` is the function `κ ↦ f(swap κ)`.
The implementation extends that function by the published principal-series
extension with the position exponents of `[induced e, induced d]`.
For a diagonal sign vector `a`, the reordered vector
`b = (a₂,a₃,a₀,a₁)` satisfies `swap diag(sgn a) = diag(sgn b) swap`.
The product of the source position characters at `sgn b` equals the product
of the target position characters at `sgn a`, by reordering the four factors.
Thus `swap_isSignCompatible` supplies the exact sign compatibility required
by `extension_transport_mem`. This gives a function in the target principal
series with finite-dimensional right compact translate span.

For the target induction block at position zero, the rotation identity
transfers every Fourier coefficient to the source position two. The
vanishing window is exactly `|j| < |e.weight|`. For the target block at
position two, it transfers to the source position zero with the window
`|j| < |d.weight|`. These coefficients vanish by membership in the source
standard module. No other positions carry induction blocks.
`mem_realStandardModule_of_unitaryCompact` propagates this compact
vanishing to all of `GL₄(ℝ)`. This proves `swap_landing`, including the
empty Fourier windows when a weight is zero.

The generic compact transport theorems then prove that `swapMap` is injective
and commutes with right translation by `O(4)`. The explicit restriction
formula proves `swapMap e d (swapMap d e f) = f`: on `O(4)` the two left
multiplications cancel, and principal-series restriction is injective.
This also proves surjectivity of the constructed map.

Finally, the published `RealKTypeCount.surjective_of_injective` applies to
any supplied injective equivariant map `T : S(d,e) → S(e,d)`, using
`swapMap e d` as the injective equivariant map in the opposite direction.
That counting theorem compares finite-dimensional polynomial degree layers
on the compact group. The proof uses no Langlands-classification premise
or external literature.

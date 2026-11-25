# Generic character crossings on a fixed compact model

This module connects the finite rational compact families to
actual Frobenius maps between fixed three-character standard modules. Its main
result retains an explicit equality hypothesis on the positive integral grid.

`CompactAction N q A` says that the actual linear map `q` preserves the compact
polynomial degree `N`, and that the compact vector of `q f` is `A` applied to
the compact vector of `f`. Such actions compose. Equality of operators on the
input vector gives equality of the actual outputs by injectivity of
principal-series restriction to the compact subgroup. Conversely, equality of
actual maps gives equality of their compact operators on actual source vectors.

`frob_action` supplies this interface for every actual rank-three Frobenius
multiplier, using degree preservation and its exact spectral realization.
For a positive natural `ell` on the generic parity class `ell ≡ eps (mod 2)`,
`inverse_integral_action` represents the inverse generic multiplier by

`P_ell(eps)^(-1) • P_ell(-i gen)`.

This identity is on the actual source model. It uses the proved reciprocal
polynomial formula on its parity class and off-parity vanishing of actual
Fourier coefficients. It makes no assertion that the polynomial is invertible
on the entire compact degree space.

`forward_data` and `inverse_data` construct the actual generic crossing and
the crossing with pointwise reciprocal multiplier in arbitrary surrounding
block lists. At a parameter with positive real part avoiding the displayed
sequence of zeros, `inverse_crossing` and `crossing_inverse` prove that these
maps are mutual inverses. `integral_nonresonant` verifies the avoidance
condition at integral generic parity.

For fixed characters `a,b,c`, `source a b c` is their three-character block
list. The maps `swap0` and `swap1` exchange its first or second adjacent pair.
With parameters `z=(x,y)`, the actual words are

`leftWord = swap0(b,c,a;y) ∘ swap1(b,a,c;x+y) ∘ swap0(a,b,c;x)`,

`rightWord = swap1(c,a,b;x) ∘ swap0(a,c,b;x+y) ∘ swap1(a,b,c;y)`.

Both have source `[a,b,c]` and target `[c,b,a]`.
`leftWord_action` and `rightWord_action` identify them with the explicit
finite rational words at the three parities
`pairParity a b`, `pairParity b c`, `pairParity a c`.
The exponents and all character modules stay fixed as the multiplier
parameters vary. These are actual compact-equivariant Frobenius maps; arbitrary
parameters need not satisfy the Lie recurrence for the fixed exponents, and
no such intertwining assertion is made.

`sourceVectors` records the actual compact vectors in a chosen degree.
Assume the two actual words agree for every parameter on the grid
`x=pairParity(a,b)+2(r+1)`, `y=pairParity(b,c)+2(s+1)`, with `r,s` natural.
For an arbitrary input, choose its finite compact degree. The actual grid
hypothesis transfers to `sourceVectors` in that degree. The proved finite
rational extension then gives equality of the compact output vectors whenever
both parameters have positive real part. Compact restriction injectivity gives
equality of actual outputs, and extensionality gives equality of the two maps.
This is `braid_of_grid`, packaged as
`RealGenericCompactCharacterStatement` and proved by
`realGenericCompactCharacter`.

All ingredients come from existing explicit multiplier formulas, actual
Frobenius data, the Fourier law and the polynomial grid extension.
The actual grid identity remains a premise. No full differential braid,
operator degeneration at poles, chosen interlaced-word comparison, or
filtration kernel-image absorption is proved by this module.

# Generic exchange of two real induction blocks

Worker 765 derives this supporting result from the actual four-crossing map,
its exact intertwining theorem, compact type transport and counting, and the
published generic rank-one multipliers. No external source or classification
result is used.

Write `L = |d.weight|`, `M = |e.weight|` and
`nu = d.exponent - L/2 - e.exponent - M/2`, so `nu + 1` is
`RealInducedPairFrobenius.swapParameter d e`.
`IsGenericPair d e` requires that these four parameters, with the indicated
parity representatives, satisfy `RealBlockMultiplier.IsGenericParameter`:

| Parameter | Parity representative |
| --- | --- |
| `nu` | `(M+1) mod 2` |
| `nu+L` | `(L+M+2) mod 2` |
| `nu+M` | `0` |
| `nu+L+M` | `(L+1) mod 2` |

For a representative `eps` equal to zero or one, that published predicate
means the parameter avoids both `eps+2m+1` and its negative for every natural
number `m`. The definition here is exactly these four conditions; it does
not assert that they characterize unlinked pairs.

`exists_multiplierData` constructs four recurrent symmetric sequences
satisfying the previously defined `MultiplierData` at the actual exponent
parameter and proves `Nonvanishing`: each sequence is nonzero on the parity
class of its crossing. To do this, `exists_multiplier` applies the published
generic multiplier existence theorem at a reduced representative, then
transfers recurrence, reflection symmetry and nonvanishing to the unreduced
representatives used by the four-crossing construction.

`blockFrobMap_injective` proves a general nonvanishing criterion for a single
actual Frobenius map. If its output is zero, its Fourier coefficient formula
forces every source coefficient in the relevant parity class to be zero.
The source sign law forces the other coefficients to be zero.
The published coefficient uniqueness theorem gives a zero source vector.
Applying this criterion to the four crossings and using injectivity of the
source inclusion gives `swap_injective`. This part works for arbitrary
recurrence parameter and supplied nonvanishing sequences.

At the actual exponent parameter, the already proved intertwining theorem
makes this exchange map equivariant for both right compact translations and
right matrix derivatives. The compact counting specialization
`RealInducedPairKTypeTransport.surjective_of_injective` then makes it
surjective. Thus `exists_bijective_intertwiner` supplies a bijective exact
intertwiner from the standard module of `[induced d,induced e]` to that of
`[induced e,induced d]`.

`inverse_intertwiner` obtains exact intertwining for the inverse by descent
through the surjective original map. Pushing the identity filtration of the
exchanged module along that inverse gives `filtration`, a one-piece adjacent
filtration of the original module. Its sole piece is the exchanged pair;
no weight inequality is needed for that alternative.
`RealInducedPairGenericFiltrationStatement` records precisely this conclusion
for all data satisfying `IsGenericPair`, and `realInducedPairGenericFiltration`
proves it. Zero weights are allowed, and no real-exponent order is assumed.

The four arithmetic exclusions remain explicit hypotheses of this supporting
statement. The result does not analyze singular multipliers or their kernels
and does not prove the unconditional `RealInducedInducedFiltrationStatement`.

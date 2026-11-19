# Summability of inverse heights of rational projective points

`Langlands.Global.projectiveTupleHeight` multiplies Mathlib's multiplicative
Weil heights of a finite tuple of projective points. The coordinate index type
can vary with the factor. Each factor and hence the product is at least one.
The empty product has height one.

Over a number field, the proof counts tuples of product height at most
`B ≥ 1`. Each factor has height at most `B`. In each factor it chooses a
nonzero coordinate of a representative and divides all coordinates by that
coordinate. The normalized vector represents the original projective point,
so the collection of normalized coordinates determines the tuple. The height
of each normalized coordinate is the height of a two-coordinate subtuple of
the representative. Mathlib's `Height.mulHeight_comp_le` bounds it by the
original projective height. If the scalar height sublevel has size at most
`C B^M` and there are `D` coordinates across all factors, the tuple sublevel is
finite and has size at most `C^D B^(M D)`.

For a height bounded below by one and with finite sublevels of cardinality at
most `C B^M`, the proof partitions the index type by `n = ⌊H(x)⌋ - 1`. In that
shell, `n + 1 ≤ H(x) ≤ n + 2`. For `s ≥ M + 2`, its contribution to the sum
of `H(x)^(-s)` is at most `C 2^M (n + 1)^(-2)`. The shifted real p-series
therefore proves summability. Applied to the tuple count, this gives
`summable_projectiveTupleHeight_rpow`. A one-factor tuple gives
`summable_projectivization_mulHeight_rpow`. In either form,
`Summable.comp_injective` restricts the series to an injectively indexed
family of projective points or tuples.

This is an internal arithmetic step for bounding Eisenstein summands by
inverse projective heights. It uses the polynomial number-field height count
proved in `NumberFieldHeightCountProof` and Mathlib's projective heights and
real p-series.

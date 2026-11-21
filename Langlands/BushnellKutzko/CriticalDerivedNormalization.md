# Bézout normalization of the shift and the residual operator

This internal arithmetic step of the proof of BK93 (2.4.1)(iii) is motivated by the normalization in §2.5. For period `e > 0` and signed degree `d`, divide by their positive greatest common divisor: write `e = h g` and `d = g k`. The integer Bézout identity provides `u, v` with `u k + v h = 1`.

For commuting units `A, π` of degrees `d, e`, respectively, the units `z = A ^ h * π ^ (-k)` and `τ = A ^ u * π ^ v` have degrees zero and `g`. Their exact identities are `τ ^ h = π * z ^ u` and `A = τ ^ k * z ^ v`. In the converse calculation, commuting operators `S, B` with the carry `S ^ h = π * B ^ u` (and `π` commuting with `B`) give `c = S ^ k * B ^ v` with `c ^ h = π ^ k * B` and `c ^ u * π ^ v = S`. These are identities in the relevant groups of units, including negative exponents; the symbol lemma separately shows that matching the symbols of `S, B` to `τ, z` matches the symbol of `c` to that of `A`.

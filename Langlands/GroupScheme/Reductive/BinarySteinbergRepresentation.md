# Actual binary polynomial representations at Steinberg degrees

This internal derived unit constructs `binaryRepresentation m`, the actual
representation of `SL(2,R)` on the monomial coordinate space of binary homogeneous
polynomials of degree `m`, for any commutative ring `R`. It converts the matrices
from `BinaryPolynomialMatrices` to linear maps by matrix-vector multiplication.

Over a field `k` of prime characteristic `p`, put `m = p^s - 1` for any natural
number `s`. The shifted binomial identity
`choose (m-c) a = (-1)^a * choose (c+a) a` holds in `k` when `c+a <= m`.
The proof casts `Nat.choose_mul` into `k`, uses the alternating Steinberg
binomial row from `RankOneSteinbergOperators`, and cancels `(-1)^c`.

The actual upper and lower root matrices at parameter `t` equal respectively
`upperMatrix k m (-t)` and `lowerMatrix k m (-t)` from
`RankOnePolynomialActions`. The proof first extracts the unique nonzero summand
in each divided-power matrix entry, then applies the shifted binomial identity.
The lower formula also uses that the square of a power of `-1` is one.
These equalities include characteristic two and degree zero.

For an infinite field `k`, the actual transvections at parameter `-t` therefore
supply `binaryPolynomialRootRealization p s`. The already proved Vandermonde
coefficient recovery and divided-power simplicity theorem then prove
`binaryRepresentation_isIrreducible`: the actual coordinate representation
has no nontrivial subrepresentation. No root-realization or irreducibility
premise is assumed here.

This is elementary derived rank-one algebra using the existing polynomial,
binomial and divided-power constructions. It does not identify an entire induced
coordinate space or establish the higher-rank Steinberg big-cell statement.

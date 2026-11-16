# Square and root conjugation for the normalized rank-one Weyl product

This internally derived calculation assumes `RingRootCell.WeylData R`, for any
commutative ring `R`, and an affine ambient group scheme. It extends the
normalized Weyl product `N` from `RankOneRingNormalizedWeyl`. Write `A(x)`
and `B(y)` for the supplied positive and negative root points, `beta` for the
pullback of the supplied unit coordinate, and `H(q)` for the coroot value
at the unit `q`.

`normalizedNegativePoint x` is `B(beta * x)`. On every scheme test over `R`,
the module proves

- `N * N = H(-1)`;
- `N * A(x) * N⁻¹ = normalizedNegativePoint (-x)`;
- `N * normalizedNegativePoint x * N⁻¹ = A(-x)`;
- `N = A(1) * B(-beta) * A(1)`.

The product `N` is the negative-positive-negative product
`B(-beta) * A(1) * B(-beta)`. Rescaling by minus one identifies it with
`H(-1) * N⁻¹`, which computes its square.

For positive-root conjugation, inverting the rank-one relation with first
coordinate minus `x` proves the identity when `1 - x` is a unit. To remove
that restriction, the total quotient ring of `R[T]` gives an injective
extension in which any element `x` is `a + b`, and both `1 - a` and `1 - b`
are units. The corresponding polynomials have a unit coefficient and hence
are nonzero divisors. Two applications of the restricted identity combine
by additivity of the root points. Injectivity on global sections and
affineness of the target descend equality on affine tests. An affine cover
then gives equality on every scheme test.

Negative-root conjugation follows by applying positive-root conjugation
twice: `N² = H(-1)`, and this coroot value acts trivially on the root
coordinates because the root-coroot pairing is two. Positive-root
conjugation at minus one gives the alternative three-factor expression.

These are conditional calculations for supplied actual Weyl and open-cell
data. They do not construct that data or identify the supplied coefficient
beta with one for an independently specified Weyl-normalized pair. The full
local Isomorphism Theorem remains separate.

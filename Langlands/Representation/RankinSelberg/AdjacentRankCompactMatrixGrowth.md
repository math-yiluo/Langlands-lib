# Uniform determinant-pole growth on compact matrix sets

This derived internal module supplies a growth estimate used in the
adjacent-rank large-twist convergence argument. Its main theorem,
`AdjacentCompactMatrix.exists_coefficient_det_growth`, assumes that the
representation `σ` of `GL_(r+1)(F)` is of Whittaker type for the standard
character associated with `ψ`, and fixes the specified Whittaker functional
`ℓ`. It chooses a natural number `N` before all actual coefficient-image
vectors `W` and all compact subsets `K` of square matrices. For each such
`W` and `K`, it then gives a real `C ≥ 0` such that

`‖W(g⁻¹)‖ |det(g)|^N ≤ C`

whenever the matrix underlying `g` belongs to `K`. Here the absolute value
and topology are the canonical ones of the supplied `PadicField`. The
representation carrier and field universes remain independent, and every
natural `r`, including zero, is allowed.

The proof uses the published
`TwoBlockLowerFixedSlice.exists_coefficient_growth`, which chooses a single
geometric base `B ≥ 1` before the coefficient vector. Choose `N` so that
`B ≤ q^N`, where `q > 1` is the residue cardinality. A continuous sum of the
absolute values of all entries is bounded on `K`. A sufficiently large
uniformizer power `ϖ^k` therefore makes every entry of every matrix in `K`
integral; this is `exists_scaled_integral_of_isCompact`.

For an invertible matrix, the adjugate of `ϖ^k g` is integral by the
published `TwoBlockConvergence.adjugate_mem_of_forall_mem`. If
`m = ord(det(g))`, then `ϖ^(m.toNat)/det(g)` is integral, as proved by
`uniformizer_pow_ord_div_mem`. The adjugate formula for the inverse now gives
`isEntryBounded_of_scaled_integral`: the entries of both `g` and `g⁻¹`
become integral at level `(r+1)k + m.toNat`. Swapping the two entry bounds
allows the published coefficient estimate to be applied to `g⁻¹`.

The scalar estimate `pow_ord_mul_abs_pow_le` bounds
`B^(m.toNat) |det(g)|^N` by `max(1, |det(g)|^N)`. For `m ≥ 0`, this follows
from `|det(g)| = q^(-m)` and cancellation; for `m < 0`, the nonnegative
part of `m` is zero. Finally, the remaining maximum is a continuous function
of the matrix determinant and is bounded on `K`. This proves the asserted
uniform determinant-pole order.

The noncomputable definition `coefficientDeterminantOrder F ψ σ hσ ℓ` chooses
one such natural order from `exists_coefficient_det_growth`. It depends on
the representation, its Whittaker-type proof, and the specified functional;
it is independent of the coefficient vector and compact matrix set.
`coefficientDeterminantOrder_spec` records its bound for each `W` and `K`.
No minimality or canonical numerical value is asserted.

The provenance is internal derivation from the imported coefficient-growth,
valuation, adjugate, and compactness results. This module asserts a growth
bound only; the actual GL Haar integrability and the closed adjacent-rank
image statement require further arguments.

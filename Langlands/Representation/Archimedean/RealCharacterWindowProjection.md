# Concrete adjacent window projections on four real characters

This internal derived module uses the published rank-one Frobenius maps and
binomial support formula, together with the compact adjacent-window spanning
theorem. No literature premise is added.

For a character pair in any surrounding lists, `low hn` is the binomial
Frobenius map composed after its pointwise-inverse Frobenius map, returning to
the original list. `high hn` is the identity minus this endomorphism.
For a positive cutoff `ℓ` with `Even(ℓ-1-pairParity c d)`,
`low_fourier` and `high_fourier` identify their compact Fourier multipliers as
the strict low-window indicator and its complement. On the correct parity
class this is the binomial nonvanishing criterion and cancellation with its
inverse. Off that parity class the original function already has zero
coefficients. Both maps commute with right compact translation, since each
Frobenius map does. No exponent order or exponent-difference condition is
required, and Lie intertwining is not asserted for these projections.

For an all-character list, `principalEquiv` is the identity on functions from
its actual compact-finite standard module to
`PrincipalSeriesAnnihilator.KFin` for its position characters. The equality
comes from the published equality of the all-character standard module and
the principal series. `transport` carries endomorphisms across this
equivalence, preserving compact equivariance. `range_sup_eq_top` therefore
applies the adjacent-window spanning theorem to the actual standard module.

For four characters `a,b,c,d`, `lowLeft a b c d m` uses the first pair, and
`highMiddle a b c d h` uses the middle pair. The proposition
`RealCharacterWindowProjectionStatement` quantifies these four characters
and positive natural cutoffs `h<m`, with the corresponding two binomial
parity conditions. It asserts that the ranges of these two concrete maps
span the entire actual four-character compact-finite standard module.
`realCharacterWindowProjection` proves it by the preceding transport and
the compact low/high multiplier identities.

This supplies concrete maps for the negative-inner-weight range route of the
filtration of the `GL_4(ℝ)` standard module of two induction blocks. Identifying
the middle-high range with an induced-block module, restricting the two-block
quotient, and proving the unrestricted filtration are not part of this module.

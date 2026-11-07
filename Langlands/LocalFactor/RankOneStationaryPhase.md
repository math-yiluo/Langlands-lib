# Finite averaging on the Gauss shell

Worker 1786 derives the Gauss twist identity by finite averaging. This is
an internal proof for the unchanged rank-one stability target, using
published lattice duality, Haar invariance, and the actual Gauss integrals.
It retains every prime, arbitrary carrier universe, supplied topology,
and supplied regular additive Haar measure.

Write `n = n(psi)`. `DeepQuotient` is the additive quotient of `L_(-m)`
by its intersection with `L_(-a)`. `deepQuotientFintype` gives it a finite
type structure using openness and compactness. `sum_deep_phases` sums
`psi.complex(z*h)` over quotient representatives, for `z in L_(n+a)`.
The sum is the quotient cardinality if `z in L_(n+m)`, and zero otherwise.
The proof descends the character and uses finite character orthogonality
and the published annihilator theorem.

Suppose `m > 0` and `chi(1+h) = psi.complex(c*h)` on `L_(-m)`.
`gauss_rotation_phase` says that rotating the unshifted Gauss integrand
by `1+h` multiplies it by `psi.complex((x-c)*h)`.
Each such unit has order zero, so its rotation preserves the shell and
the integral with respect to the same supplied Haar measure.
`gauss_integral_localized` averages these equal integrals over
`DeepQuotient`. Orthogonality shows that the integral equals its
localization to `x-c in L_(n+m)`. The finite phase-weighted integrands
are integrable: each is continuous on the compact shell away from zero.
The exchange with the integral is a finite sum of integrable functions;
the proof does not require a product integral.

If `a = m+k` and `ord(c) = ord(x) = -(n+a)`, the localization condition
implies `x/c in U^k`, as proved by `localized_ratio_mem`. Thus every
quasicharacter `eta` of conductor at most `k` takes the same value on
`x` and `c`. `gauss_twist_on_localized` gives the integrand multiplier
`eta(c^(-1))` there.

Finally, `gauss_integral_twist` assumes the conductor of `eta` is at most
both `k` and `m`. The second bound makes `eta(1+h)=1` on the averaging
lattice, so the same linearization applies to `chi*eta`. Localize the
two integrals and use the first bound for twist constancy. This proves
the unshifted integral identity with multiplier `eta(c^(-1))`, with
the identical supplied Haar measure on both sides.

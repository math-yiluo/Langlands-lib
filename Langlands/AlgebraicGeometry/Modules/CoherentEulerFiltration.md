# Coherent filtrations and Euler polynomial telescoping

`CoherentFiltration X n` records an actual filtration of coherent module
sheaves of length `n`. Its terms are indexed by `Fin (n + 1)` and its graded
factors by `Fin n`. It records that the initial term is zero, arrows from each
term to its successor and then to the corresponding factor, their zero
composites, and short exactness. Each term and factor is quasicoherent and has
finite sections over every affine open. `CoherentFiltration.complex` constructs
the actual short complex at one step; `complex_shortExact` verifies its short
exactness. This bundle makes explicit the data used in the existing
`CoherentIntegralIdealFiltrationStatement`, without assuming that such a
filtration exists or that its factors are integral ideal pushforwards.

Every strict support bound for the final term is equivalent to the same bound
for every graded factor. The proof inducts along `Fin (n + 1)`: the zero term
has every support bound, and the bound for a short exact middle term is the
conjunction of the bounds for its two outer terms. The conclusion also holds
for length zero. This uses the actual closed-support theorem
`hasSupportDimensionLT_shortExact_iff`.

For a proper structure morphism to the spectrum of a field, an actual line
bundle `L`, and any common Newton truncation `d`,
`coherentEulerPolynomial_last` identifies the Euler polynomial of the final
term with the finite sum of the factors' Euler polynomials.
`coherentEulerPolynomial_eq_sum` transports this identity to any coherent sheaf
isomorphic to the final term. These statements require no support bound,
noetherianity, separatedness, ampleness, or polynomial reconstruction premise.
They concern the published Newton truncations of the actual twisted Euler
characteristics.

The proof applies the published short-exact-sequence additivity at every step.
Each factor polynomial is the difference of successive term polynomials.
Summing these differences telescopes because the first term's polynomial is
zero. The two standard decompositions of a sum over `Fin (n + 1)`, at its first
and at its last index, supply the telescope. `coherentEulerPolynomial_coeff_last`
then applies coefficient extraction to this finite polynomial sum.

`coherentEulerPolynomial_coeff_nonneg_and_pos_iff` is a transfer lemma at a fixed
`d`: suppose every factor's coefficient of degree `d` in its truncation at `d`
is nonnegative, and is positive precisely when the factor fails
`HasSupportDimensionLT` with strict bound `d`. Then the final term has the same
two properties. A finite sum of nonnegative rational numbers is positive
precisely when some summand is positive, and the support equivalence turns
this existential condition into failure of the support bound for the final
term. The `_of_iso` variant transports the conclusion to an isomorphic endpoint.
No upper support bound is needed for this transfer itself; a geometric
application must prove the factor hypotheses under its own upper bound.

This is an internal construction and derivation from the published coherent
Euler polynomial, its additivity, the actual support-bound exactness theorem,
and finite-sum identities. It neither constructs integral ideal filtrations nor
proves the factor positivity premises. In particular it does not prove the
ample positive-leading-term target by assuming a new outer certificate.

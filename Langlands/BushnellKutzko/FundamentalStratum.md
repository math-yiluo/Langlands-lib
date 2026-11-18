# Fundamental strata, their polynomials, and split and nonsplit strata

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, §2.3, definition of
fundamental strata and `y_b`, printed p. 57; definition of `φ_b` and
Definition (2.3.3), printed p. 58 (PDF pp. 69–70).

`Stratum.IsFundamental S` means `r = n−1` and no element of the
existing coset `b + 𝔓^{1−n}` is nilpotent. It uses `IsNilpotent`
in the actual endomorphism ring.

`RingPrimeElement O` is a nonzero generator of `Ring.jacobson O`.
For `O = 𝒪[F]`, the published
`jacobson_integer_eq_maximalIdeal` identifies that ideal with `𝔭_F`.
For `O = subfieldIntegers F E`, it is definitionally the published
`𝔭_E`. Thus it represents the prime elements in both intended
integer rings without a separately supplied valuation on `E`.

`Stratum.fundamentalElement S π` is
`π^(n/g) • b^(e/g)` as an endomorphism of `V`, where
`e = S.chain.period` and `g = Nat.gcd e S.n.natAbs`.
Here `gcd(e,|n|) = gcd(e,n)`; the exponent `n/g` is an integer
exponent of the nonzero scalar in `K`, and `e/g` is a natural
exponent of the endomorphism. The scalar commutes with `b`,
so this is the source's `b^(e/g) π^(n/g)`.

`Stratum.fundamentalPolynomial S π` is the characteristic polynomial
over `K` of that endomorphism, reduced coefficientwise to
`O/Ring.jacobson O`. The source explicitly gives this construction
as an alternative to the characteristic polynomial of the induced
endomorphism of `L₀/L_e` (p. 58): `y_b ∈ 𝔄`, its characteristic
polynomial has integral coefficients, and the reduction is `φ_b`.
Finite-dimensionality for the characteristic polynomial is obtained
from the published lattice chain.

`reduceIntegralPolynomial` constructs the coefficient reduction by
lifting each nonzero coefficient to `O`, then applying the quotient
map. In the injective integer-ring inclusions each lift is unique;
for the `y_b` of a stratum every coefficient is integral. A
coefficient with no lift is assigned zero so the definition remains
total for arbitrary input polynomials. That default never applies
to a coefficient of `y_b` in the intended setting.

`Stratum.IsSplit` requires fundamentality and two distinct monic
irreducible divisors of `φ_b`. Monic normalization makes
“distinct” mean distinct irreducible factors up to association.
`Stratum.IsNonsplit` requires fundamentality and an equality
`φ_b = p^m` for a monic irreducible `p` and a positive integer `m`.
Each property quantifies a prime element, as the source chooses
one. Changing that prime scales `y_b` by a residue-field unit;
the factorization properties are unchanged. No theorem asserting
exhaustiveness, independence of choices, equivalence invariance or
classification is built into these definitions.

All definitions use the same general `O,K,V` parameters as `Stratum`.
Consequently they also apply to strata in `End_E(V)` with the
published ring of integers and lattice-chain mechanism over `E`.

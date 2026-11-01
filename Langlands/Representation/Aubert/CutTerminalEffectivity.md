# Actual terminal quotients and the common-sign class

This internal adapter applies the published finite exact-sequence Euler
argument to the actual signed cut complex. Its provenance is the exact
Grothendieck relation for actual image and quotient representations, together
with the cut-indexed Aubert expansion proved in `CutEulerExpansion`.

`finiteDifferential` is exactly `degreeMorphism` between the actual degree
objects. Adding the finite-length witnesses changes neither the carrier nor
the action nor the differential. `terminalObject A hA 0` is the actual degree
zero object. At successor degree `i+1`, it is the actual cokernel of the
degree `i` differential, with finite group-algebra length inherited through
the surjective quotient projection. These are the terminal objects constructed
by `SmoothRep.FiniteExactEuler`.

`ConcentratedAt F T A m` is an explicit proposition about these actual maps
and carriers. It requires injectivity of the first differential only if
`m > 0`, equality of the incoming range with the outgoing kernel at degree
`i+1 < m`, and subsingleton degree carriers above `m`. This module does not
prove those representation-theoretic conditions.

For `m+1 ≤ n`, `alternating_truncated_expansion` discards the degrees above
`m` from the full Aubert class expansion. Their carriers are subsingleton,
so their classes vanish in the existing exact Grothendieck group.
`signed_alternating_terminal_class` then applies the published descending
Euler-class identity: multiplication by `(-1)^(n-(m+1))` gives exactly the
class of the surviving actual terminal quotient. All actual short exact
relations, including nonsplit ones, remain in force.

`effective_of_concentration` applies the published composition-factor map
to this equality. The class of the finite-length terminal quotient has
nonnegative coefficients because they count actual composition factors.
The quotient need not be irreducible or nonzero. When the inducing block
length is `b=m+1`, the resulting sign is the required common `(-1)^(n-b)`.
The single-term case `m=0` uses no injectivity hypothesis.

`effective_rankZero` handles the empty rank separately. The published actual
rank-zero Aubert operator is the identity and natural subtraction gives the
support sign one. Therefore every actual finite-length rank-zero input has
effective image, without any concentration hypothesis.

All declarations preserve arbitrary primes, the supplied p-adic field and
topology, independent field and carrier universes, and the saturated carrier
universe `max uF uV`. This adapter does not prove the concrete support
filtration, graded-map comparison, or concentration for constituents of
quasicuspidal induction. Those are still needed to obtain the unconditional
`SignedEffectivityStatement`. No irreducible-image or classification assertion
is an input here.

# Scalar compatibility of prime-power extraction on actual Tate twists

This module bundles the existing prime-power coordinate maps on actual
roots-of-unity limits as continuous semilinear maps over the canonical
profinite-integer projections. It works over an arbitrary commutative ring
`R`, with a prime natural number `p` expressed by `[Fact p.Prime]`.
The excluded modulus `m : ℕ` in the away construction is arbitrary; extraction
at `p` requires `h : Nat.Coprime p m`.

All declarations are in `Langlands.TateTwist.Divisibility`.
The definitions of the roots-of-unity levels, limits, scalar actions, and
topologies are imported unchanged from `Twist`, `TwistDivisibility`, and
`TwistPrimeComparison`. The scalar ring maps are the published
`Global.ProfiniteIntegerRing.toPadic p` and
`Global.PrimeToProfiniteIntegerRing.toPadic p m h` from
`ProfiniteIntegerPadicProjection`.

## Selected and full limits

For a predicate `P : ℕ → Prop` and
`hP : ∀ n : ℕ, P (p ^ n)`, the existing `toPrime R P p hP` reads the
coordinates at \(p^n\), including \(n=0\), of a coherent family in
`Integral R P`. The theorem `toPrime_smul` proves

\[
\operatorname{toPrime}(a\cdot x)
 =\operatorname{toPadic}_p(a)\cdot\operatorname{toPrime}(x)
\qquad (a\in\widehat{\mathbb Z}).
\]

The source action is the existing `fullModule` on every selected limit.
The target action is the existing \(\mathbb Z_p\)-module structure on
`TateTwist.Integral R p`. At exponent \(n\), the source action uses the
residue of \(a\) modulo \(p^n\), while the target action uses the reduction
of `toPadic p a` modulo \(p^n\). The proof applies subtype extensionality
and function extensionality, rewrites the latter residue using
`ProfiniteIntegerRing.toZModPow_toPadic`, and closes by definitional
equality. In particular it does not choose generators of the roots of unity.

`toPrimeSemilinear` packages the same additive homomorphism as a semilinear
map over `ProfiniteIntegerRing.toPadic p`.
`toPrimeContinuousSemilinear` adds continuity from the previously proved
`continuous_toPrime`, for the existing product-subspace topologies.
Their `_apply` lemmas identify the underlying functions with the original
coordinate map by reflexivity.

Specializing `P` to the always-true predicate gives `fullToPrime_smul` and
`fullToPrimeContinuousSemilinear`. Its `_apply` lemma identifies the latter
with `fullToPrime R p`. No new scalar action or topology is installed.

## Away limits

For `h : Nat.Coprime p m`, the theorem `awayToPrime_smul` proves

\[
\operatorname{awayToPrime}(a\cdot x)
 =\operatorname{toPadic}_{p,m,h}(a)\cdot\operatorname{awayToPrime}(x)
\qquad (a\in\widehat{\mathbb Z}^{(m)}).
\]

Here \(\widehat{\mathbb Z}^{(m)}\) denotes the actual
`PrimeToProfiniteIntegerRing m`, the limit of residue rings at positive
moduli coprime to \(m\). The source action is the existing `awayModule`.
The proof has the same coordinate argument as the full case, using
`PrimeToProfiniteIntegerRing.toZModPow_toPadic`. The witness
`h.pow_left n` makes \(p^n\) an allowed away coordinate.

`awayToPrimeSemilinear` and `awayToPrimeContinuousSemilinear` package this
law over the away scalar projection, with continuity supplied by
`continuous_awayToPrime`. Their `_apply` lemmas state that the underlying
maps are exactly `awayToPrime R p m h`.

## Restriction, naturality, and product coordinates

`awayToPrimeContinuousSemilinear_restrictAway` states pointwise that
restricting a full root family to the away indices and then extracting
prime-power coordinates gives the full extraction. This follows by
reflexivity. The corresponding scalar projections are compatible by the
imported `PrimeToProfiniteIntegerRing.toPadic_restrict`.

For every commutative ring `S` and ring homomorphism `f : R →+* S`,
`toPrimeContinuousSemilinear_map` and
`awayToPrimeContinuousSemilinear_map` give pointwise naturality:
applying `f` to each root before extraction gives the same element as
applying the existing prime-adic `TateTwist.map p f` after extraction.
These are definitional equalities of the existing coordinate maps.
The full case is a specialization of the selected-limit formula.

Finally, `toPrimeProduct_smul_apply` gives the scalar formula at each
`q : Nat.Primes` for the existing map `toPrimeProduct`.
`toAwayPrimeProduct_smul_apply` gives the corresponding formula at each
`q : AwayPrime m` for `toAwayPrimeProduct`. Their proofs specialize the
two scalar laws above. These are coordinate identities; the module does
not introduce a new action on either prime product.

## Provenance and scope

This is an internal compatibility construction derived from the published
root limits and their finite residue actions, the published extraction
maps, and the exact reduction formulas of the canonical p-adic scalar
projections. The implemented proofs are described above. No new claim
is attributed to original literature.

The construction requires no field, characteristic, invertibility, finiteness,
or enough-roots hypothesis beyond those stated above. It proves neither rank
nor an isomorphism with a product of prime-adic twists. Rational comparisons,
restricted products, geometric monodromy, and Weil pairings are separate
constructions. In particular this module supplies no trivialization of a
twist and no complete abelian-scheme or PEL specialization.

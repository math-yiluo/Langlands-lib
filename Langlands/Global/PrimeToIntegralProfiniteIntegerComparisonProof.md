# Integral away comparison for every supplied normalized full comparison

Worker 18 proves
`Langlands.Global.PrimeToIntegralProfiniteIntegerAdeleComparisons` by the theorem
`Langlands.Global.primeToIntegralProfiniteIntegerAdeleComparisons`. Its result is
exactly the imported proposition, with no outer parameters or additional
hypotheses. The target is unchanged. The imported completion-comparison module
exports its existing density lemma for reuse here, with the same statement and proof.

The proof is an internal construction from the published residue-limit rings,
their canonical p-adic projections, and the actual integral restricted-product
adele rings. It adapts the prime-power injectivity argument of Worker 205's
`ProfiniteIntegerPadicProductComparisonProof`, the product and completed-integer
identifications of Worker 212's `IntegralFiniteAdelePadicProduct`, and reuses
Worker 18's integer-density proof in `ProfiniteIntegerCompletionComparisonProof`.
Workers 205 and 212 are credited for these adapted components. No additional
literature statement is asserted.

## Retained primes and places

For each natural modulus `m`, `away_place_iff` proves that a finite place `v`
is retained precisely when its corresponding natural prime is coprime to `m`.
Mathlib identifies that prime with `natGenerator v` and characterizes its
divisibility into `m` by membership of the integer `m` in the image of `v.asIdeal`
under the ring-of-integers equivalence with the integers. Transporting membership
back along that equivalence and using prime coprimality proves the assertion.
This argument applies to every natural number `m`.

The private `awayPlaceEquiv` restricts Mathlib's `primesEquiv` to the retained
indices. The private `awayIntegralProductEquiv` identifies the product of
completed integer rings at those places with the existing integral away
subring. Its forward map is the restricted product's `structureMap`; its inverse
reads each coordinate together with its integrality proof. These functions are
inverse by definition. Forward continuity is the continuity of `structureMap`
into the actual restricted-product topology, followed by the subspace topology
of the integral subring.

Reindexing and the existing continuous local equivalences
`adicCompletionIntegers.padicIntEquiv` give `awayPadicIntegralEquiv`, a ring
equivalence from the product of p-adic integer rings at the retained primes to
the integral away adeles. Its forward continuity is proved coordinatewise.

## The canonical away map and injectivity

`awayPadicProduct` takes the product of the existing canonical maps
`PrimeToProfiniteIntegerRing.toPadic`. Composing it with
`awayPadicIntegralEquiv` gives `awayComparison`. Both component maps are
continuous, so this is a continuous ring homomorphism for the existing
topologies. Its integer normalization follows from preservation of integer
casts and the diagonal rational algebra map.

To prove injectivity, fix a retained positive modulus `n` and integer
representatives `z` and `w` for the residues of two families at `n`.
`ZMod.intCast_eq_intCast_iff_dvd_sub` reduces equality to divisibility of their
difference by `n`; `Int.natCast_dvd` passes to its natural absolute value.
`Nat.dvd_iff_prime_pow_dvd_dvd` reduces this to every prime power `p^k` dividing
`n`.

When `k = 0`, the divisibility assertion is immediate. Otherwise `p` divides
`n`, and coprimality of `n` with `m` implies that `p` is retained. Equality of
the p-adic product images gives equality of the `toZModPow k` reductions.
The published prime-to projection formula and the residue-family compatibility
at `p^k ∣ n` identify these reductions with `z` and `w` modulo `p^k`.
The divisibility criterion now proves equality at `n`, and residue extensionality
proves equality of the two original families.

## Compatibility with the supplied full witness

The imported `residue_integer_dense` proves that the canonical integers are dense
in the full residue-limit ring. An open neighborhood restricts only finitely many residue
coordinates. Take their product as a positive modulus, choose an integer
representative of the given family's residue there, and use divisibility
compatibility to match every specified coordinate. This yields an integer in
every nonempty open subset.

Fix the supplied full equivalence `eFull`, its continuity, and its integer
normalization. The two maps from the full residue ring to integral away adeles
are

```text
awayComparison m ∘ PrimeToProfiniteIntegerRing.restrict m
primeToIntegralRestriction m ∘ eFull.
```

Both are continuous. They agree on integers: restriction preserves integer
casts, `awayComparison` has the integer normalization, and restriction of the
full diagonal adele is the away diagonal adele. The dense-range equalizer
principle into the Hausdorff target proves equality of these functions.
This establishes the restriction identity against exactly the supplied
`eFull`; no alternate full witness is chosen.

## Surjectivity and the final equivalence

`integralRestriction_surjective` extends an integral away adele by zero at all
omitted places. The resulting family belongs to the product of all completed
integer rings; the published `integralFiniteAdelesProductEquiv` turns it into
an actual full integral adele whose restriction is the original one.

For any integral away adele, choose this full lift `b` and take
`PrimeToProfiniteIntegerRing.restrict m (eFull.symm b)` in the source.
The just-proved compatibility and the inverse identity of `eFull` show that
its image under `awayComparison` is the requested adele. Thus `awayComparison`
is surjective. Its injectivity follows from that of `awayPadicProduct` and the
product-to-integral ring equivalence.

`RingEquiv.ofBijective` supplies the final equivalence with this forward map.
Forward continuity was proved above; inverse continuity follows from the
existing compactness of the residue-limit source and Hausdorffness of the
integral away target. The final tuple contains both continuities, integer
normalization, and the exact compatibility identity. The supplied hypothesis
that `eFull.symm` is continuous is allowed but is not needed by this argument.

All natural moduli are covered. At `m = 0`, no prime or finite place is
retained and the only retained positive residue modulus is one; the same
injectivity and zero-extension arguments apply. At `m = 1`, all primes and
places are retained. No primality, positivity, or nontriviality hypothesis on
`m` is introduced. All helper declarations are private, and the proof makes no
rational tensor comparison claim.

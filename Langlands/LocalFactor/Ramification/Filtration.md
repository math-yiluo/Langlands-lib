# Ramification through maximal-ideal quotients

Worker 40 implements the congruence filtration of a group acting on a local
ring. This is an independent construction layer for subsequent specialization
to the actual integer ring of a finite Galois extension of local fields in
the paired `Galois` module.

For a commutative local ring R with maximal ideal m, `CongruenceQuotient R n`
is the actual ring R/m^n. `quotientAction` descends the given ring action to
this quotient. Every ring automorphism preserves the unique maximal ideal
and all its powers; the implementation proves this before forming the map.
`congruenceGroup R G n` uses Mathlib's existing ideal inertia construction.
It is proved equal to the kernel of the quotient action.

`lowerGroup R G i` uses the exponent i+1. Its zeroth group is exactly the
ideal inertia group, and its groups are normal and decreasing.
`lowerGroupInt` extends the indexing to integers, with the whole group at
-1 and, by the stated implementation convention, at every smaller integer.

For a finite group acting faithfully on a Noetherian local ring, Krull's
intersection theorem implies that the intersection of the congruence groups
is trivial. Each nonidentity element therefore leaves some congruence group.
Finiteness gives one common bound, and monotonicity makes every subsequent
group trivial. This termination proof is needed to construct finite
conductor sums. No termination assumption or arbitrary cutoff is supplied.

## Sources and scope

Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67 (1979),
Chapter IV, section 1, Lemma 1 and Proposition 1, printed pages 61–62,
retained PDF pages 68–69. Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Serre defines the lower groups through their action on the actual
integer-ring quotients. The general local-ring formulation here is a derived
implementation of that condition. Serre uses a monogenic integer ring to
prove termination; this implementation instead uses Krull intersection.

All dependencies are from the pinned Mathlib environment, commit
`5ed2965256430c3649e86755f9576b54eca72435`: ideal inertia and its subgroup
laws, induced quotient equivalences, maximal-ideal preservation, and
`Ideal.iInf_pow_eq_bot_of_isLocalRing`. No project theorem or definition is
imported. This generic module alone does not identify an arbitrary ring
action with a local Galois group; the local-field specialization must supply
the actual field automorphisms acting on its actual integer ring.

This file is submitted together with `Conductor` and `Galois` as one
coherent construction. Independent review and publication are recorded
separately from development compilation.

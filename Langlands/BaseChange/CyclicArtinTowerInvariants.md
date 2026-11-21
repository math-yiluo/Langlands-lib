# Ramification identities in a finite Artin conductor comparison

For a tower of finite p-adic fields with `M/K` and `M/E` Galois, the
relative automorphism group embeds into `Gal(M/K)`. Its index is `[E:K]`
by the Galois cardinality and degree formulas. The two inertia orders
are the ramification indices of `M/K` and `M/E`. The proof compares the
maximal-ideal power in the actual integer ring with Mathlib's
ramification index and uses the inertia cardinality theorem.

The residue degree of `E/K` is the group index times the ratio of the
`M/E` and `M/K` inertia orders. The proof uses the residue-cardinality
formulas in the tower and the identity `e f = [M:K]` and its relative
version. For a common lower-group cutoff, Hilbert's different formulas
and different-ideal transitivity give the difference of the two
lower-group order sums. This is `e(M/E) d(E/K)`, where `d(E/K)` is
the trace-codifferent exponent. The results use the supplied
p-adic topologies and valuation relations throughout.

The arithmetic follows Serre, *Local Fields* (1979), Chapter III,
§4, Proposition 8, and Chapter IV, §1, Propositions 1 and 4. The degree
formula is Chapter II, §2, Corollary 1 of Proposition 3. The theorem
`finiteArtinTowerRamification` proves both equalities in
`FiniteArtinTowerRamificationStatement` for the supplied tower. They
serve as inputs to the cyclic norm character conductor comparison.

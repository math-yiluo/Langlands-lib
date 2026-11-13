# Actual Tits indices from positivity on simple restrictions

Author: Worker 244 for Task 6244.

This internal helper constructs an actual `TitsIndexData` with a prescribed
Galois pinning, a ground-field maximal torus, and a maximal split torus
factoring through it. Its additional hypothesis
`GaloisPinningData.SimpleRestrictionsPositive` says that each actual simple
root restricts either to zero or to a character pairing strictly positively
with the supplied cocharacter of the split torus.

The hypothesis supplies neither all-root compatibility nor genericity.
The constructor proves both. A positive absolute root is built by adding
simple roots. Induction shows that its restriction is zero or has positive
pairing: zero restrictions contribute zero, and positive pairings add.
Applying this to a root or its negative proves that every nonzero
restriction pairs nontrivially and has exactly the sign specified by the
prescribed base. Every actual relative root is the nonzero restriction of
an absolute root after the torus splits over the separable closure. This
published root-restriction comparison supplies genericity for the actual
relative roots.

`restrictionHom` is the additive map on the full character lattice obtained
by pulling back to the base-changed split torus and descending through its
canonical character-lattice equivalence. The constructor retains the
supplied pinning, tori, inclusions, factorization and cocharacter. In
particular it retains the actual root restrictions and actual Cartan matrix.

Provenance: internal. The root-sign lemmas are direct consequences of
Mathlib's positive-root addition induction. The constructor combines them
with the Library's actual splitting-field root-restriction comparison.
It does not assert that a particular classical group satisfies the simple
restriction hypothesis, nor prove Task 6244's antihermitian computation.

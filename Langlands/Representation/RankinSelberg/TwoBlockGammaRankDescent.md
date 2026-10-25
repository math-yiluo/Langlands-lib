# Conditional algebraic core of two-block gamma descent

This is an internal helper for Worker 393's task
`9b03c738-dddb-431b-8858-2c0ae56b9958`. It abstracts the two descending
inductions in JPSS (1983), section 7, printed 438–442, into a symmetric
commutative-group-valued function on a rank-indexed family. Indices are actual
positive ranks minus one. The operation `ind x y` retains the order of the two
inputs; its index `b + 1 + a` is their total rank minus one. This arithmetic
order makes `ind mu pi` have index `r + 1` definitionally when `mu` has index
zero. It imposes no equality between induced representations in different
orders.

The implemented cancellation lemma compares the enlargement identity for the
original two blocks with the corresponding identity after swapping the pair.
It rewrites the identities for each block and the auxiliary rank-one object,
regroups four factors in the commutative group, and cancels the auxiliary
product. The first descending induction fixes the second block index and
handles the case where the first block has index zero. Its top case is the
adjacent base. Below it, the dominant and rank-one bases provide the opposite
factorizations. The second descending induction fixes both original block
indices; its top case is the dominant base, and its step uses the first
induction for all three opposite factorizations.

This file does not establish any analytic premise. The three bases, symmetry,
a rank-one object, closure under the actual normalized induction, and a
consistent choice of certified gamma units still must be instantiated on
full Whittaker-type representations in a carrier universe closed under
induction. This algebra is not the requested closed multiplicativity proof.
There is no claimed lower-to-upper representation comparison: the eventual
instantiation must use the exact upper-convention analytic base conclusions,
whose proofs own the actual reversal and conjugation obligations.

Provenance: internal algebra extracted from the registered original
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
section 7, printed pages 438–442. The route retains each pair as a certificate,
so neither a character-twist identity nor a high-ramification argument is
part of this algebra. The algebra establishes only its stated implication
and supplies none of its representation-theoretic or analytic premises.

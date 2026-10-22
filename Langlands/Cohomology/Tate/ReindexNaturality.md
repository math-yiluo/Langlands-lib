# Naturality of Tate reindexing

Original proof: Worker 45. Audit and documentation: Worker 25.

This module extends the actual complex reindexing of `Reindex`. A commuting
coefficient square induces a commuting square of Tate complexes: the proof
uses evaluation on cochains in nonnegative degrees and on single chains in
negative degrees. Applying Mathlib's homology functor gives coefficient
naturality in every integer degree.

For a map of short exact coefficient sequences along a finite group
isomorphism, the three complex maps form a map of short exact complexes.
Mathlib's naturality theorem for its homology connecting maps therefore proves
compatibility with the actual Tate connecting homomorphisms. Neither sequence
is required to split.

The degree-zero formula compares the actual short complex at zero with
invariants modulo the norm image. Its induced kernel map is precisely the
coefficient map on invariants, and its induced cokernel map sends an invariant
class to that image. This proves the representative formula for reindexing.
No subgroup transitivity theorem is asserted by this module alone.

These are internal functoriality proofs for the construction documented in
`Reindex.md`, rather than additional axioms. The norm-splice conventions are
those of Serre, *Local Fields* (1979), Chapter VIII, section 1, printed
pp. 127–129 (PDF pp. 133–135), and the pinned Mathlib Tate complex.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

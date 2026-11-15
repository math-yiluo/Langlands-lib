# Negation and negative bases of integral root data

This internal construction defines simultaneous minus identity on both full
lattices of an integral root datum. Its root permutation sends each root to
its negative. It is an involution and commutes with every full root-datum
automorphism, including on central lattice directions.

The proof of height transport expands a root as an integral combination of
simple roots, transports this sum by a root-datum equivalence, and reindexes
the finite sum. This is the root-datum part of the published
`SplitPinning.Iso.height_eq` argument. Applying it to negation shows that the
mapped base has precisely the opposite positive roots. Its simple support
consists of the negatives of the original simple indices.

The construction uses Mathlib's root-index negation, equivalences and base
transport. It assumes neither a group realization nor a classification theorem.

# Euler sequences of coherent modules twisted by line bundles

This internal prerequisite defines the actual Euler sequence
`n ↦ χ(X, M ⊗ L^n)` over a field, for a proper scheme, a quasi-coherent module
`M` with finite sections on every affine open, and an actual line bundle `L`.
Its values are rational casts of the integral Euler characteristic of derived
cohomology. Proper coherent cohomology finiteness supplies the required
finiteness and eventual vanishing for every twist; the rank-one tensor closure
supplies quasi-coherence and finite affine sections.

The functor `tensorBy L` uses the explicit sheafified tensor in the second
variable. It is naturally isomorphic to the right tensor functor in the
published monoidal module category. A line bundle is tensor-invertible,
so left tensor is an equivalence. Braiding identifies left and right tensor,
and the explicit comparison identifies right tensor with `tensorBy L`.
Thus tensor by a line bundle is an equivalence, and it preserves short exact
sequences.

The actual cohomological Euler characteristic is invariant under module
isomorphisms and additive on short exact sequences with finite cohomology.
Applying these results after each line-bundle twist proves the corresponding
identities for the Euler sequences. A zero module has zero sequence.
The explicit tensor associator identifies `(M ⊗ L) ⊗ L^n` with
`M ⊗ L^(n+1)`, so twisting `M` once shifts its sequence by one.

The provenance is internal: the constructions and arguments specialize the
existing actual tensor, rank-one invertibility, proper coherent cohomology and
Euler additivity results. This module proves no polynomial degree bound or
positivity assertion.

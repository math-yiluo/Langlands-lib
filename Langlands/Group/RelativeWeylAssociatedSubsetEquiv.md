# Associated-subset reindexing

Worker 196 constructs `Langlands.Group.RelativeWeylIndexing.associatedSubsetEquiv`
for every finite Coxeter system, with independent universes for the simple
labels and the group. It permutes all finite subsets of the labels, including
the empty subset. Its value at `J` is exactly the published
`associatedSubset cs J`, and its cardinality is `J.card`.

This is an internal construction from the published intrinsic Coxeter proofs.
It supplies the finite reindexing needed after representation-class
comparisons in the proof of Aubert contragredient commutation. It makes no
assertion about reductive groups, actual root signs, or normalized functors.

The proof first shows that the longest representative for the associated
subset is the inverse of the original longest representative. Write `d` for
`longestRep cs J`, and let `b` have maximum length in the standard subgroup
`W_J`. Minimal-representative decomposition and length additivity show that
`b*d` has maximum length in the whole group. The published
`associatedSubsetLaws_proof` identifies `W_K` for `K = associatedSubset cs J`
with `d⁻¹ W_J d`. Inversion of the minimality inequalities makes `d⁻¹` left
minimal for `W_K`. Length additivity on both sides then shows that
`b' = d⁻¹*b*d` has the same length as `b`. For any left-minimal `x` for
`W_K`, the bound on the length of `b'*x` gives `length x ≤ length d`.
`longestRepresentativeUnique_proof` identifies `d⁻¹` with `longestRep cs K`.

Unfolding the two simple images and cancelling conjugations proves that the
associated-subset operation is an involution. Injectivity of the simple
reflections is supplied by `simple_injective`. `Function.Involutive.toPerm`
turns this involution into the displayed equivalence. Cardinality preservation
is exactly the second clause of `associatedSubsetLaws_proof`.

The proof uses `exists_minimal_in_doubleCoset`,
`length_mul_of_left_minimal`, `associatedSubsetLaws_proof`, and
`longestRepresentativeUnique_proof` from the published finite Coxeter
modules. There are no representation-theoretic dependencies and no new
assumptions about root-system realization.

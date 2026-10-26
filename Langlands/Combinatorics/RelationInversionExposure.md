# Exposing a relation inversion by unrelated swaps

Author: Worker 494.

This internal combinatorial API formalizes the exposure step in Zelevinsky
(1980), Section 6.7, printed p.190 (PDF27): an inversion may be made adjacent
using the unlinked neighbor transpositions of Section 6.4(1), printed p.189
(PDF26). The registered source is `zelevinsky-1980-induced-ii`, PDF SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The generalization to an arbitrary acyclic relation and its auxiliary order
extension are internal derived content, not assertions attributed to the source.

`UnrelatedAdjacentSwap R l l'` exchanges one neighboring pair for which both
relation directions are false, leaving the prefix and suffix in place.
`UnrelatedSwapReachable R l l'` is the reflexive transitive closure, so zero
swaps are permitted. Reachability preserves all list occurrences up to
permutation and preserves the inversion count. It also transports any predicate
closed under these swaps.

`exists_adjacent_relation_of_inversions_pos` requires a decidable relation,
a positive inversion count, and explicit acyclicity: the transitive closure of
`R` has no self-loop. It produces a reachable list with an adjacent `R` pair.
It does not require transitivity of `R` or distinctness of list entries.
The result includes empty lists through its positive-count hypothesis.

The proof extends the strict transitive closure of `R` to an auxiliary linear
order, using Mathlib's order extension theorem. Insertion sorting in descending
order would remove every `R` inversion. If every reachable list lacked an
adjacent `R` pair, every sorting swap would be unrelated in both directions:
the forward direction is excluded by that supposition, and the reverse
direction by the auxiliary strict ordering. The invariant then retains both
reachability and the original inversion count through sorting, contradicting
the original positive count. The intermediate theorem
`relationInversions_eq_zero_of_closed` states this invariant argument for any
supplied linear-order key that strictly increases along `R`.

This is an auxiliary definition/API contribution. It supplies no segment
acyclicity, linkage orientation, integral-twist freeness, induced-product
isomorphism, embedding, ordered socle, or exhaustion theorem. To specialize it
to segment precedence, those mathematical inputs must be proved separately;
identifying unrelatedness with nonlinkage requires linkage orientation.
The auxiliary linear order is a combinatorial choice and asserts no analytic
exponent or classification result. All imports are elementary combinatorics and
order theory, including `RelationInversions`; no representation theorem enters.

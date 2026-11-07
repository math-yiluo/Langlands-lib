# Minimal matching of rank-one segment members

This internal support module combines finite occurrence matching with the
scalar-uniformizer norm of a cuspidal class. It makes no claim about induction
maps, sphericality, or existence of segment constituents.

`coordinateMember d` reads the source segment and its member number using the
actual consecutive-block coordinates of a segment product datum. For segments
of cuspidal rank one, `coordinateMember_content` proves that the multiset of
all these coordinates is exactly the datum's cuspidal content, with every
occurrence retained. The proof rewrites finite lists as sums of singleton
multisets, reindexes the sum by the block-coordinate equivalence, and uses the
rank-one size equality to obtain each segment's content.

`exists_minimal_matching` assumes rank-one source segments, a target block
shape all of whose block sizes are one, and a target tuple with the same
cuspidal content and weakly decreasing scalar-uniformizer norms. It produces
an actual minimal double-coset representative matching every source member to
a target occurrence. The norm strictly decreases as the member number increases
within any segment. Applying the existing sorted matching lemma to the dual
order of the real numbers gives the result. No ordering of the source segments
or distinctness of target classes or norms is required. The proof works in
independent field and representation-carrier universes.

The finite-tuple multiset identity is reused from
[`Langlands.Algebra.MultisetOfFn`](../../Algebra/MultisetOfFn.md) through
`SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum`.

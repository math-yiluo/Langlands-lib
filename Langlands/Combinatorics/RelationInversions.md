# Relation inversions on finite lists

Author: Worker 494.

This internal counting API isolates the numerical part of Zelevinsky (1980),
Section 6.7, printed p.190 (PDF27). The registered source is
`zelevinsky-1980-induced-ii`, PDF SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The definitions and generalization to an arbitrary decidable binary relation
are internal derived content. They assert no representation theorem.

`relationPairCount R l r` sums one for every pair of occurrences, one in each
list, satisfying `R`. `relationInversions R l` counts related occurrences in
increasing positional order. Entries need not be distinct, and no property of
`R` is assumed. The proofs split these finite sums under concatenation.
An inversion count of zero is equivalent to the pairwise nonrelation condition.

The adjacent-swap identity shows that the only changed contribution is that
of the two swapped occurrences. It gives equal counts when neither relation
holds, and a strict decrease when only the original forward relation holds.
The replacement lemma allows the middle list to change length. A strict decrease
inside that list and nonincrease of each outside occurrence's contributions
imply a strict decrease in the whole list. Its hypotheses explicitly expose
the comparisons that segment union/intersection geometry must later prove.

This module uses only elementary list and natural-number arithmetic. In
particular it does not supply linked-segment geometry, an embedding into any
induced product, ordered socle existence, or multisegment exhaustion. It does
not depend on segment heads, analytic classification, or any other
representation-theoretic conclusion. All counts include repeated occurrences,
and the empty lists are included.

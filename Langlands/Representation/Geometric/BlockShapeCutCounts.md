# Counting cuts and edges inside ordered blocks

Author: Worker 320.

This derived supporting unit builds on the block-shape cut equivalence.
`interiorBoundary n` embeds a cut index `i : Fin (n - 1)` into the boundary
positions `Fin (n + 1)` by adding one. `B.uncuts` is the complement of
`B.cuts` among the possible interior edges.

The boundary membership and finite-set identities reconstruct the composition
boundaries from the two endpoints and the image of `B.cuts`. Their proofs
separate the two endpoints; any other boundary has the unique cut index one
smaller than its positive position. Conversely, cut membership supplies that
boundary.

`cuts_card` proves `B.cuts.card = B.length - 1`. At rank zero, the block
length and cut type are both zero. At positive rank, the two endpoints are
distinct and outside the shifted cut image, so the composition's boundary
cardinality is the cut cardinality plus two. Mathlib's boundary cardinality
law then gives the result.

`uncuts_card` proves `B.uncuts.card = n - B.length`, again with rank zero
handled explicitly. It subtracts the cut cardinality from the cardinality
`n - 1` of all possible interior edges. The final intrinsic sign law rewrites
the integer weight `(-1) ^ (n - B.length)` as `(-1) ^ B.uncuts.card`.

These are consequences of the existing positive block sizes and the cut
definition, using Mathlib's composition boundaries and finite-set counts.
They provide the number of internal edges used in finite alternating sums.
They assert no relation with Weyl-subgroup refinement and prove no
representation-theoretic identity or segment classification.

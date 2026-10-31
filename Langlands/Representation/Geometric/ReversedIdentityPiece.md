# The actual inverse-reversal geometric piece

Author: Worker 526, adapting the published full-refinement assembly by
Worker 289 and reusing the published reversal transport constructions.

`Langlands.Geometric.reversedIdentityGeometricPieceEquiv` constructs an
actual representation equivalence from the geometric piece at the raw
permutation `B.reversePermutation.symm`, pulled back along the actual
reversed-label Levi equivalence, to the original smooth representation `A`.
The source shape is `B`, the target is `B.reverse`, and the actual source and
target refined-intersection Levi equality witnesses `hS`, `hR` are retained.
Every refinement satisfying those equalities is allowed. Field and
source-carrier universes are independent, and all ranks, including zero,
are included. There is no irreducibility, cuspidality, admissibility,
analytic, support, scalar-action, dimension or minimality premise.

## Implemented construction

The private whole-conjugation assembly uses only the published
`AssociatedGeometricPiecesEquivalenceProof` constructions. Whole-Levi
conjugation makes both actual intersection Levis full, so the supplied
Levi equalities make both refined Levis full. The published
`fullRefinedJacquetEquiv` identifies the actual source normalized refined
Jacquet action with the source restricted to that full subgroup. The
published equality-relabeling and `intersectionTransportFullEquiv` maps
carry it through the actual middle factors. The published
`fullRefinedInductionEquiv` then evaluates normalized induction from the
full target. Its actual inverse-half source and positive-half target
moduli are one by the public full-refinement identities. This yields the
actual whole-Levi transport of the original smooth source, without a
supplied comparison or quasicuspidality hypothesis.

For the requested raw piece, the public `conjugatesLevi_reverse` and its
inverse give the whole-Levi conjugation. A private matrix-embedding
calculation identifies the forward reversal Levi conjugation with the
inverse of `leviReverseEquiv B`. The public `transport_inv` therefore
identifies the piece's whole-Levi transport with restriction along this
inverse reversed-label map. Pulling back along `leviReverseEquiv B` cancels
it. The underlying linear equivalence is the constructed whole-conjugation
piece equivalence; its intertwining equation after pullback follows from
the inverse law of the actual Levi equivalence.

## Provenance and scope

This is internal composition of public actual maps. The full-refinement
assembly follows the implemented proof by Worker 289 in
`CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`; only its
unneeded source hypotheses are absent from this new explicit data interface.
The present unit does not assume or generalize the published theorem by
ignoring hypotheses: it constructs the equivalence directly from the public
helper definitions, which have no such hypotheses. The block-reversal
construction is the published one, and it is not assumed involutive.
No new literature theorem is asserted.

The module identifies an individual actual piece. It constructs no geometric
filtration, occurrence-exclusion theorem, generalized-block splitting or
projector, identity-cell quotient map of the whole induction, whole-induction
isolation or Hom comparison. Those remain separate obligations.

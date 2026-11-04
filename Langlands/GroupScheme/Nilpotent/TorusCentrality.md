# Torus centralizers in nilpotent groups

Author: Worker 1487.

This internal derivation concerns a smooth connected affine group scheme over
an arbitrary field, with the existing geometric nilpotence predicate. For
any split torus and any homomorphism from that torus to the group,
the all-test torus centralizer is the entire group and the homomorphism is
central. The homomorphism need not be closed or injective.

The implemented proof uses the full weight-zero Lie space from
`Nilpotent.TorusWeights`, identifying the differential invariants of the
conjugation action with the full actual Lie algebra. A splitting isomorphism
identifies the acting torus with a diagonalizable group scheme. The published
rigidity theorem for diagonalizable actions applies: the fixed subgroup has a
smooth closed representative, and its full Lie image in the smooth connected
ambient group implies that this fixed subgroup is the entire group. For
conjugation, it is exactly the torus centralizer. Its all-refinement
commutation property gives centrality on all test schemes.

`IsNilpotentGroupScheme.splitTorusCentralizerIso` identifies any group scheme
representing this centralizer with the ambient group. Its forward homomorphism
is the originally supplied representing inclusion. It reuses the existing
isomorphism between representatives of the full subgroup functor.

All fields and group schemes are in arbitrary universe `u`, with no
characteristic restriction. This construction is derived from the Library's
actual weights, actions and representing-subgroup interfaces, and makes no new
translation of a literature assertion. Nonsplit descent, construction of a
maximal torus, and the unipotent quotient remain separate obligations.

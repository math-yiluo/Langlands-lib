# Base change and rigidity of homomorphism families

Worker 798, with Worker 329.

This internal module pulls back natural homomorphism families parametrized by a
group scheme and reflects equality with the identity-parameter family through a
flat surjective base change. `HomFamily.baseChange` uses the actual point
adjunctions of the parameter, source and target. Multiplicativity and naturality
follow from their counterparts for the original family.

For reflection, pull back each test scheme and use its projection to the original
test. Flatness and surjectivity make this projection an epimorphism. Naturality
identifies precomposition of the original family with evaluation of the pulled
back family; canceling the projection gives equality over the original test.
This is the same descent argument used by Worker 329 for actions in
`MultiplicativeTypeConnectedActionReduction`, generalized to two distinct source
and target groups and without action laws in the parameter.

`eq_one_of_diagonalizableRigidity` applies the supplied
`DiagonalizableRigidityStatement` hypothesis through the universal natural-family
bridge. The rational base point of the parameter group is its identity. This
conditional result retains all finite-type, finite-generation and connectedness
hypotheses of that rigidity proposition. The module currently proves no
unconditional rigidity theorem.

The constructions and proofs are derived infrastructure. The source of the
supplied rigidity proposition is Milne, *Algebraic Groups* (2017), Theorem 12.36,
printed p.243, as recorded in the published statement module.

`eq_one_of_commonSplitting` extends this conclusion to any source and target
which become diagonalizable over a supplied common field extension. The
parameter group remains connected over that field by the published
`GroupScheme.connectedSpace_baseChange_of_connected`; its finite-type
properties persist by base change. The diagonalizable case applies there, and
the flat surjective reflection lemma descends the equality. This theorem
assumes actual diagonalizing isomorphisms over the common field. It does not
construct such a field from separate multiplicative-type witnesses.

# Closed subgroups of groups of multiplicative type

Author: Worker 1232.

These are derived helpers for the full-center multiplicative-type reduction.
They use the existing `IsMultiplicativeType`, actual field base change,
and the proved `Diagonalizable.closedSubgroupPresentation`.

`IsMultiplicativeType.of_iso` transports the splitting presentation through
the base change of an actual group-scheme isomorphism.
`IsMultiplicativeType.of_isClosedSubgroup` base changes the given closed
inclusion to the splitting field and composes it with the diagonalizing
isomorphism. The existing closed-subgroup presentation theorem then supplies
an actual diagonalizable model with finitely generated character group.
This proves the result over the same splitting field.

`exists_diagonalizableIso_of_isClosedSubgroup_splitTorus` gives the stronger
presentation over the original field when the ambient group is already a
split torus. It identifies that torus with the diagonalizable group of the
free character group `I → ℤ` and applies the same closed-subgroup theorem.

Every result retains the full closed subgroup scheme. No smoothness,
connectedness or reducedness assumption is added, and the resulting character
group may have torsion. The provenance is this internal derivation from the
published diagonalizable closed-subgroup proof and the explicit splitting
definition. These helpers supply no reductive-center structure theorem or
quotient-existence assertion.

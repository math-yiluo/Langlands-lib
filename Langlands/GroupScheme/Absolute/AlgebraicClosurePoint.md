# The algebraic-closure test scheme

`Langlands.GroupScheme.algebraicClosurePoint k` is the test object
`Spec (AlgebraicClosure k) → Spec k`, formed by applying `Over.map` to the
identity object over the algebraic closure. It is defined for every field
in universe `u` and asserts no additional mathematical property.

This common module contains the identical test-object construction used in
`GeneralLinearBorelProof` and `RegularCocharacterSolvable`. The former keeps
`GeneralLinear.UpperTriangular.closurePoint` as an abbreviation for it. The
construction and its mathematical meaning are unchanged.

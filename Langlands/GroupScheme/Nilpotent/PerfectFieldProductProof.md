# Products of unipotent groups and tori over perfect fields

This module proves the unchanged Library proposition
`Langlands.GroupScheme.NilpotentPerfectFieldProductStatement.{u}` in every universe.
For every perfect field and every smooth connected affine group scheme over it,
geometric nilpotence is equivalent to an actual group-scheme isomorphism with a
product of a smooth connected affine unipotent group and a torus.

The forward proof uses the published perfect-field sectioned solvable torus
quotient, applied to the solvability implied by geometric nilpotence. The two
statement inputs of that construction are discharged by `solvableTorusQuotient`
and `RelativeRoot.splitUnipotentStableVectorSubgroup`. Its specified geometric
unipotent radical is smooth, connected, and unipotent, and is affine because it
is a closed subgroup of the affine ambient group. Its quotient is a torus and
has a homomorphic section. The full scheme kernel of the quotient equals the
range of the radical inclusion on every test scheme.

The section composed with the quotient is the identity, so multiplication of
the section and the radical is a scheme isomorphism by
`isIso_subgroupMultiplication_of_isIso_comp`. The section is central by
`IsNilpotentGroupScheme.isCentral_of_isTorus`, including on nonreduced test
schemes. Consequently `commutingSubgroupMultiplicationHom` upgrades this
multiplication to a group-scheme homomorphism. The forgetful functors reflect
its isomorphism property in two steps, from relative schemes through monoid
objects to group objects. Inverting and interchanging the factors gives the
required order, unipotent group followed by torus.

For the converse, the abstract group of points of the unipotent factor on every
relative scheme test is nilpotent by `isNilpotent_points_of_isUnipotent`; its
affineness and smoothness supply the finite-type hypotheses. The torus factor
is commutative by `IsTorus.isCommMonObj`. Their product is nilpotent. The product
point equivalence and the given group-scheme isomorphism transport this to the
ambient group on the geometric-point test. `baseChangePointsEquiv` identifies
this with exactly the point group in `IsNilpotentGroupScheme`.

This is an internal deduction from the imported, published Library theorems.
The external mathematical target is Milne, *Algebraic Groups* (2017), Corollary
16.48, as documented with its source correspondence and dated errata in
[the unchanged statement](PerfectFieldProductStatement.md). The implemented
route uses the geometric unipotent radical and a torus-quotient section rather
than reproducing Milne's separable trigonalization argument. No extra hypotheses
on the field, the torus, or the characteristic are introduced.

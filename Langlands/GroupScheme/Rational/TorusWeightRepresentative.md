# The connected representative of a coordinate weight subgroup

This module is an internal construction from the existing coordinate
weight subgroup, its quotient representative, and the identity component
of a smooth affine group scheme. Work over an arbitrary field `k` in
universe `u`. Let a group-valued functor `F` on commutative `k`-algebras be
corepresented by `B`, let `σ : TorusAction F I` be an actual split-torus
action with finite index type `I`, and assume that `B` is formally smooth
and of finite type over `k`. Let `P` be any additive subsemigroup of
`I → ℤ`, including the empty semigroup and those containing zero.

The quotient `B ⧸ weightIdeal e σ P` is smooth by
`smooth_quotient_weightIdeal`. The existing `cutGroupScheme` construction
therefore gives a smooth affine closed subgroup representing the
coordinate weight subgroup on every test scheme. This module uses that
representative unchanged and defines `connectedWeightGroupScheme` as its
actual identity component. `connectedWeightHom` is the composite of the
identity-component inclusion and the quotient subgroup inclusion.
Its source is smooth, affine, connected, and geometrically connected, and
its underlying scheme map is a closed immersion. Its all-test range is
thus a smooth connected closed represented subgroup and lies in the
original coordinate weight subgroup.

The general lemma `tangentSubmodule_range_identityComponent_comp`
proves that replacing a smooth affine subgroup by its identity component
preserves its intrinsic tangent image in an affine ambient group, provided
the subgroup homomorphism is monomorphic on underlying schemes over the
field. One inclusion follows from containment of the all-test ranges.
For the other, write a tangent vector as an image under the differential
of the subgroup inclusion using `tangentSubmodule_range`. The
identity-component inclusion is open, hence smooth. The published
`Lie.targetMapLinear_surjective_of_smooth` lifts the tangent vector
through this inclusion. Postcomposition gives a point in the tangent
image of the connected subgroup. Applying this lemma gives
`tangentSubmodule_range_connectedWeightHom`, with no assumption of
equality of coordinate weight spaces and intrinsic action weight spaces.

For any connected group scheme `K`, a homomorphism to the ambient
corepresented group whose all-test range lies in the coordinate weight
subgroup factors through `connectedWeightHom`. The construction
`connectedWeightFactor` first uses the existing represented-subgroup
factorization `IsRepresentedBy.liftOfLE` to reach the quotient
representative and then `IdentityComponent.factor` to reach its identity
component. The composite equation is proved, and monicity of the closed
inclusion makes this factorization unique. In particular its range is
contained in the range of `connectedWeightHom`.

These are derived constructions and proofs using the published
`CorepresentedClosedSubgroup`, `CorepresentedSmooth`,
`TorusWeightSmoothGeneral`, `IdentityComponent`, `TangentImage`,
`SmoothDifferential`, and `ParabolicLieCriterion` interfaces. They do not
identify this coordinate construction with the generated all-test
`RelativeRoot.semigroupSubgroup`, prove stability of its identity component,
or establish the exact action-weight Lie image, general maximality,
uniqueness by Lie weights, or split unipotence. Those remain separate
obligations of the full semigroup-realization theorem.

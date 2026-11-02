# Scheme representatives of subgroup functors

This is an internal categorical construction for the fixed-subgroup
representability proof. Its provenance is the Yoneda equivalence for group
objects in Mathlib, applied to the published `SubgroupFunctor` interface.
It asserts no geometric representability theorem.

For a subgroup functor `F` of a group scheme `G` over an arbitrary scheme `S`,
`toFunctor` is the group-valued presheaf of its points, and `inclusion` is its
natural inclusion into the points of `G`. Suppose a monomorphism `i : Z → G`
of schemes over `S` has the following property on every test scheme: a point
belongs to `F` if and only if it factors through `i`. Then postcomposition by
`i` gives a set-valued representation of `F`. Injectivity uses the monomorphism
and surjectivity uses the stated pointwise factorization.

`representingGroupScheme` equips this same `Z` with its group-object structure
through `GrpObj.ofRepresentableBy`. Full faithfulness of the group-valued
Yoneda embedding produces `representingHom`. Evaluation of the Yoneda identity
at the identity point of `Z` proves that its underlying scheme morphism is
exactly `i`. Hence it represents the original subgroup functor. If `i` is a
closed immersion, the induced homomorphism is a closed subgroup scheme, and
`isClosedRepresentable_of_scheme` gives the published closed-representability
predicate.

All hypotheses refer to actual schemes and morphisms, and all point
comparisons range over every scheme over `S`. The construction has no field,
smoothness, affineness, or finite-type restriction.

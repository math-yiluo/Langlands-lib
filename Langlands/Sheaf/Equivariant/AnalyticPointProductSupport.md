# Compact support lifting for analytic point products

This internal specialization of `PointProductSupport` proves its compact
separating bounds for the actual field-valued points of an analytic étale site.
It uses the published theorem that open analytic domain inclusions are étale
and the actual point axioms, through `etalePointLifting_of_openDomains`.

The inverse image of a closed subset of the underlying analytic space satisfies
`SeparatesComplement`: its open complement is an étale object, point lifting
supplies a fiber element there, and naturality of the underlying-point
projection shows that every point with a fiber there avoids the closed subset.
The identity étale object is terminal, which identifies the lifted fiber element
over it with the prescribed one.

On a Hausdorff underlying space, a compact subset of field-valued points has
compact closed image. Its full inverse image is a compact enlargement for the
induced topology and has the separation property just proved.
`etaleCompactSections_pointProduct_map_surjective` therefore applies the
generic support-preserving lifting theorem to every coefficientwise surjection.
It concerns the actual germ supports and the actual `etaleCompactSections`
functor; surjectivity of the field-point projection is not needed.

The construction is derived from the imported Library interfaces, with no
additional literature assertion. Derived compact acyclicity and the effect of
equivariant induction and the smooth coreflector remain further obligations.

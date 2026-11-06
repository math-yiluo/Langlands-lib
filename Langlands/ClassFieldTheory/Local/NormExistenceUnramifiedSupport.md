# Unramified norm groups below overgroups of integral units

These are derived supporting lemmas for the norm-subgroup existence theorem.
They retain the arbitrary field universe of `PadicField`.

`mem_subgroup_of_index_dvd_ord` considers any subgroup `H` of the multiplicative
group containing the integral-unit subgroup for supplied topological data `T`.
If the normalized order of `a` is divisible by `H.index`, then `a` belongs to
`H`. Choose a field unit `b` with order equal to the quotient integer. Then
`b ^ H.index` belongs to `H` by the group index theorem. The ratio
`a / b ^ H.index` has order zero and hence is an integral unit, which proves
the claim. The lemma does not assume finite index; when the index is zero its
premise forces order zero.

`exists_unramified_normSubgroup_le` considers a finite-index subgroup `H`
containing the canonical integral units. It produces a finite intermediate
extension in the actual algebraic closure, abelian over the base and
unramified in the canonical ramification-index sense, whose degree is
`H.index` and whose determinant norm subgroup is contained in `H`.
The already proved unramified extension theorem supplies an extension of that
positive degree. Its arithmetic Frobenius coordinate makes its Galois group
cyclic, hence abelian. The published unramified norm-membership theorem
identifies its norms with the elements whose order is divisible by this
degree. The first lemma puts every such element in `H`.

The provenance is the composition of the published
`unramifiedExtensionDegreeExistence`,
`arithmeticUnramifiedCoordinateExistence`, and `unramifiedNormMembership`,
together with the actual order-zero unit and filtration constructions and
Mathlib's `Subgroup.pow_index_mem`. This isolates the integral-unit
overgroup input needed by the generic compact-subgroup criterion. It asserts
containment of a norm group, and leaves the finite norm-lattice argument
needed for equality to its caller.

The Prop-valued declaration `UnramifiedNormSubgroupContainment` packages the complete assertion above. Its lowercase theorem proves the assertion using the preceding supporting lemmas. The entry assertion and these proofs are supplied together for review.

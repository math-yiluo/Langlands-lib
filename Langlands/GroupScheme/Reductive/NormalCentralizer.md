# The full centralizer of a normal subgroup

Worker 1466, with the centralizer proof route proposed by Worker 1454.

This is an internal construction from the published all-test fixed-subgroup
representability theorem. It adds no structural theorem about semisimple groups.

For any base scheme and homomorphism `j : H ⟶ G`,
`mem_conjugation_fixedSubgroup_iff` identifies the fixed subgroup of the
conjugation action with points commuting with `j(H)` after every change of test
scheme. `conjugation_fixedSubgroup_isNormal` proves that this full centralizer
is normal if the all-test image of `j` is normal. On a refined test, conjugate
an element of `j(H)` by the inverse ambient point, use normality to lift it to
`H`, and conjugate the resulting commutation equation back.

`range_le_conjugation_fixedSubgroup_iff` characterizes containment of an actual
subgroup map in this full centralizer by commutation on every test scheme.
The reverse direction uses the naturality of the image subgroup functor.

Over an arbitrary field in universe `u`, `exists_closed_normal_centralizer`
assumes that `H` is affine and that the image of `j` is normal. It applies
`fieldFixedSubgroupRepresentability` to `AutomorphicAction.conjugation j`.
The resulting group scheme `K` and map `i : K ⟶ G` have closed inclusion,
image equal to the full fixed subgroup, normal image, and pointwise commutation
with `j(H)` on every scheme over the field. No smoothness, connectedness,
semisimplicity, or finite-type hypothesis is used in this construction.

The full centralizer is not asserted to be smooth. Multiplication of `H` with
this centralizer is not asserted to cover `G`; that is a separate structural
obligation in the semisimple normal-complement argument.

`ClosedNormalCentralizer j` bundles the actual representing group scheme,
its closed inclusion, its equality with the full fixed-subgroup image,
normality, and all-test commutation. Under the same affine-source and
normal-image assumptions, `closedNormalCentralizer j hj` chooses such a
bundle from `exists_closed_normal_centralizer` using classical choice.

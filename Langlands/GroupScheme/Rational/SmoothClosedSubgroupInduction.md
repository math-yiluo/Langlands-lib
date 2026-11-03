# Induction on smooth closed subgroups

This internal unit supplies induction on proper smooth affine closed subgroups
over any field in universe `u`. No connectedness, reductivity or characteristic
hypothesis is used.

`closedSubgroupSupport j hj` is the closed range of a closed-subgroup inclusion
`j : H ⟶ G` in the underlying space of `G`. The range is closed because the
underlying scheme map is a closed immersion.

`noetherianSpace_of_smooth_affine` proves that a smooth affine group scheme over
a field has a Noetherian underlying space. Smoothness implies local finite type
over the Noetherian field spectrum; the source is affine and hence compact.
Mathlib then supplies the Noetherian-space instance.

`closedSubgroupSupport_comp_lt` proves that a proper closed subgroup of a smooth
group has strictly smaller support after any closed embedding in an ambient
group. Range inclusion gives the weak inequality. The reverse inclusion would
make the subgroup map surjective, using injectivity of the ambient closed
embedding. A surjective closed immersion into a reduced scheme is an
isomorphism. The Library's `SmoothReducedProof.isReduced_of_smooth_over_field`
gives reducedness, and the forgetful functors from schemes over the field,
monoid objects and group objects reflect the resulting isomorphism. This
contradicts properness, which here means `¬ IsIso i`.

`smoothAffineGroup_closedSubgroup_induction` applies the well-founded strict
order on `TopologicalSpace.Closeds G.X.left` in a fixed smooth affine ambient
`G`. At each support it proves the property for every smooth affine group
closed-embedded with that support, using the preceding strict-decrease lemma
for the induction hypotheses. The identity embedding gives the result for
`G`. The step premise quantifies over all proper smooth affine closed
subgroups; the theorem adds no geometric structure or conjugacy assertion.

This construction is internal, derived from existing Mathlib scheme and
topological APIs and the published smooth reducedness proof. Worker 1305
proposed the fixed-ambient support route, and Worker 1295 implemented it.

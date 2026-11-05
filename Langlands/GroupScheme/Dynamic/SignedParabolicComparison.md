# Signed dynamic parabolics and actual contracting subgroups

This internal module provides an actual isomorphism construction and three general lemmas used in the quotient-curve
approach to the rank-one Borel problem. It does not classify Borels or assume a
rank-one classification.

`Dynamic.centralizer_groupHom_neg` says that a cocharacter and its negative
have the same dynamic centralizer on every test scheme. Precomposing with
inversion gives each inclusion, and applying inversion twice proves equality.

`Dynamic.parabolic_neg_eq_top_of_unipotent_eq_bot` applies to a smooth connected
affine group over any field, a split torus map, and a torus cocharacter. If the
positive contracting subgroup functor is trivial, its tangent submodule is
zero. The published signed tangent spanning formula then says that the
centralizer and negative contracting tangent submodules span the ambient Lie
algebra. Both lie in the negative dynamic parabolic. The actual affine
representative of that parabolic is a smooth closed subgroup, so surjectivity
of its differential makes its inclusion an isomorphism. This proves equality
with the full group functor on every test scheme. The argument uses a smooth
closed representative; it does not assert that arbitrary Lie containment
implies subgroup containment in positive characteristic.

`Dynamic.negativeParabolicIsoOfUnipotentEqBot` constructs the resulting
isomorphism from the explicit affine representative of the negative dynamic
parabolic to the ambient group. It applies uniqueness of representatives to
the full subgroup functor and the identity presentation of the group.

`Dynamic.parabolic_le_of_unipotent_le_of_centralizer_le` works over any scheme
base with separated ambient group. The actual limit decomposition writes a
point of the dynamic parabolic as the product of a contracting point and a
centralizer point over the same test scheme. It therefore gives parabolic
containment whenever both of these subgroup functors are contained.

These are derived internal consequences of the published dynamic limit,
smoothness, representability, signed tangent spanning and smooth subgroup
equality results imported by this module. No new source theorem is postulated,
and no general Borel or parabolic classification is used.

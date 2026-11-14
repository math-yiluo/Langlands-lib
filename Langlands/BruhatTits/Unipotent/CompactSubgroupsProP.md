# Compact subgroups of actual dynamic unipotent point groups

This internal prerequisite specializes the compact-unipotent pro-p theorem to the actual
identity-limit subgroup `Dynamic.unipotent χ`. The ambient group is an affine group scheme
locally of finite type over a nonarchimedean local field `F`, at an arbitrary universe.
Smoothness, reductivity and splitness are not required.

`unipotentPointsHomeomorph` identifies the rational points of the existing closed
representative `Dynamic.Affine.unipotentScheme χ` with `unipotentPoints χ`, the evaluation
of the original dynamic subgroup functor at the identity test scheme. The representative
and ambient rational points carry their canonical evaluation topologies, and the subgroup
has the inherited topology. The construction is the existing
`rationalPointSubgroupHomeomorph` specialized to the published dynamic representative;
it does not choose a different rational-point subgroup or topology.

`unipotentPoints_eq_range` evaluates the published representability equality at the
identity test scheme. Consequently the actual dynamic point subgroup is exactly the
range of `rationalPoints.map (Dynamic.Affine.unipotentHom χ)`.

`isProPSubgroup_of_isCompact_le_unipotentPoints` proves that any compact subgroup of the
ambient rational points contained in this dynamic point subgroup is pro-p for
`ringChar 𝓀[F]`. The closed inclusion and the ambient finite-type structure morphism
make its representative locally of finite type. The published
`dynamicUnipotentUnipotence` proves that this representative is unipotent, without an
extra structural premise. The preceding literal range equality then permits application
of `isProPSubgroup_of_isCompact_le_range_of_isUnipotent`.

These are internal constructions and consequences of the published dynamic
representability and unipotence theorems and the compact-unipotent and closed-image
transfer prerequisites. They supply a local input to the chamber argument for corrected
KP Proposition 13.5.2; they do not assert a chamber normalizer or the full maximal pro-p
classification.

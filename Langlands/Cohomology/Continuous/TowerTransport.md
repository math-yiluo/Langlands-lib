# Continuous cohomology transport for subgroup towers

This internal construction makes explicit the change of subgroup coordinates
needed for transitivity. It applies to every natural degree, arbitrary common
universe, a topological group, and a jointly continuous discrete module.
Compactness, Hausdorffness, and finite index are not needed.

For subgroups `K ≤ H` of `G`, Mathlib's
`Subgroup.subgroupOfContinuousMulEquivOfLe` identifies the group `K.subgroupOf H`
with the original subgroup `K`, including their inherited topologies.
`continuousTowerCoefficientIso` identifies restriction of the coefficients along
this equivalence with successive restriction to `H` and then `K.subgroupOf H`.
It is the identity on the coefficient module; the two actions are definitionally
the same.

`continuousTowerCohomologyIso` applies the published
`continuousCohomologyIso` to that continuous group equivalence and coefficient
identification. Its source is Mathlib's actual continuous cohomology of `K`, and
its target is the same cohomology functor on the nested restriction. Its forward
map is exactly `ContinuousCohomology.map` for the group equivalence and identity
coefficient map. The inverse and both inverse certificates come from the
published equivalence transport.

`continuousRestriction_comp_tower` proves that direct restriction from `G` to `K`
followed by this transport equals successive restriction from `G` to `H` and to
`K.subgroupOf H`. The proof combines the actual cochain maps by functoriality.
The two composite group maps coincide pointwise and both coefficient maps are
identities. Applying homology gives the claimed equality.

For open subgroups, `towerOpenSubgroup K H` packages the preimage of `K` under
the inclusion of `H` as an open subgroup of `H`. Its underlying subgroup is
exactly `K.toSubgroup.subgroupOf H.toSubgroup`. This supplies the nested open
subgroup needed as a later corestriction argument.

The provenance is internal: the construction specializes the Library's proved
equivalence transport and Mathlib's continuous subgroup equivalence, and the
restriction certificate follows from Mathlib's cochain composition law. This
file does not construct corestriction or assert its transitivity.

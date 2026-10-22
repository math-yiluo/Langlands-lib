# Finite stages in subgroup tower coordinates

Worker 22. This construction supplies the finite-stage coordinate map required
to compare direct and iterated transfer. It does not assert a transfer law.

Let `K ≤ H` be open subgroups of a topological group `G`, let `N` be an
open normal subgroup of `G`, and let `A` be a genuine discrete continuous
module over a commutative topological ring `k`. All types are in an arbitrary
common universe. No compactness or containment of `N` in `K` is needed here.

`towerQuotientHom` sends the quotient of `K.subgroupOf H` by the pullback
of `N` to `K/(N ∩ K)`. It is induced by the actual subgroup equivalence,
not an identification of the quotient types. `towerFixedCoefficient` sends
each fixed vector to the same vector with its fixedness proof expressed in
the nested subgroup coordinates; quotient induction proves equivariance.
`finiteTowerCochains` uses these maps in ordinary inhomogeneous cochains,
and `finiteTowerCohomology` is its actual induced homology map.

The continuous cochain map `continuousTowerCochains` uses the continuous
subgroup equivalence and the already published identity coefficient
isomorphism. Its homology map is the existing
`continuousTowerCohomologyIso.hom`.

The certificate `finiteTowerCochains_comp_stage` says that finite-stage
inflation commutes with this continuous coordinate map. Its proof cancels
the injective comparison to ordinary cochains, applies its published
naturality, and identifies the two composite group and coefficient maps.
The cohomology certificate `finiteTowerCohomology_comp_stage` follows by
homology functoriality and naturality of the homology isomorphism for
forgetting coefficient topology. It covers every natural degree, including
zero, on Mathlib's actual continuous cohomology.

This is internal transport infrastructure derived from the published
`TowerTransport`, finite-stage comparison, and Mathlib's cochain
functoriality. The coordinate maps and their compatibility certificates are
derived here directly from these constructions; no separate result from
the literature is asserted.

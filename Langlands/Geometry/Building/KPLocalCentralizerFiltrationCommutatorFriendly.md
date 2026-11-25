# Commutator friendliness of the torus filtration over `K = F^ur`, from the coroot formula

This helper for clause 1 of `QuasiSplitLocalTorusFiltrationStatement` (KP Lemma 7.2.3
over `K`) is used, through `KPLocalCentralizerTorusFiltrationClauses`, by
`KPQuasiSplitLocalTorusFiltrationProof`. It imports the published statement
`KPLocalCorootComponentStatement`. The final proof supplies the helper's premise with
the published theorem `kpLocalCorootComponent` from `KPLocalCorootComponentProof`.

Lean module: `Langlands.Geometry.Building.KPLocalCentralizerFiltrationCommutatorFriendly`.

## Declaration

`B.centralizerTorusFiltration_isCommutatorFriendly_of_coroot hZ hcor` uses the binders of
`KPLocalMoyPrasadGroups` (`B : MaximalUnramified.BuildingData F H`,
`hZ : IsTorus B.centralizer.Z`) and assumes `KPLocalCorootComponentStatement` (`hcor`).
It shows that the filtration of `KPLocalMoyPrasadGroups`
`Z(K)_r = B.centralizerTorusFiltration hZ r` satisfies clause 1 of
`QuasiSplitLocalTorusFiltrationStatement`, in the form of
`ParahoricBuildingData.CentralizerFiltration.IsCommutatorFriendly` with `B` in place of
`P`. The hypotheses are: a point `x`, a relative root `a`, nontrivial `u ∈ U_a(K)` and
`u' ∈ U_{-a}(K)`, and `0 < r` with `r = x.val a u + x.val (-a) u'`. If
`u'⁻¹ u u' u⁻¹ = v' · j(z) · v` with `v' ∈ U_{-a}(K)` and `v ∈ U_a(K)`, then `z ∈ Z(K)_r`.

## Proof

Apply `hcor` to `B`, `hZ` and `a`. It gives an induced torus `T_a`, a morphism
`f : T_a ⟶ B.centralizerTorus hZ`, and `c ∈ T_a(K)` with `f(c) = z` and `r ≤ ω(χ(c) - 1)`
for every geometric character `χ`. Since `r > 0` and `T_a` is induced,
`mem_localTorusFiltration_of_induced` gives `c ∈ T_a(K)_r`. By functoriality
(`map_localTorusFiltration_le`), `f(c)` lies in `localTorusFiltration F (B.centralizerTorus hZ) hZ r`,
and that subgroup is by definition `B.centralizerTorusFiltration hZ r`.

## Provenance

This is an internal consequence of the published coroot statement, the induced-torus
characterization and torus-filtration functoriality. It implements the commutator clause
of Kaletha–Prasad (2023), Definition 7.2.1 and Lemma 7.2.3 (printed pp.245–246).
The target's source correspondence is documented in
`KPQuasiSplitLocalTorusFiltrationStatement.md`.

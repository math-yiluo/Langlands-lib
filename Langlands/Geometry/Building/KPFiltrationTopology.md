# Compact open actual root filtrations

For actual `B : ValuationBuildingData G`, this module packages each
`U_{a,x,r}` as `filtrationOpenSubgroup`, an open subgroup of the actual root
group `U_a(F)`, assuming only `B.apartment.IsTopologyCompatible` (V 7).
It proves compactness of this subgroup in its root-group topology and of
the same set in the canonical ambient topology `rationalPointTopology F G.X`.
It also proves compactness of the doubled-root filtration and of the actual
two-factor real-depth block.

All fields have arbitrary universe `u`. The nonarchimedean local field may
have either characteristic. Root-indexed conclusions quantify over actual
relative roots, so they introduce no positive-rank assumption.

The construction uses the existing actual root subgroup, its filtration,
and the subspace topology from `G(F)`. V 7 supplies exactly relative
openness and algebraic boundedness. It does not assert that a root
filtration is open in the ambient group.

This is a derived topology adapter for KP Definition 6.1.2, V 7, printed
p.199 / PDF p.230, and Definition 2.2.1 and Fact 2.2.3, printed p.70 /
PDF p.101, in *Bruhat–Tits Theory: A New Approach* (2023). The
1 November 2024 corrections, PDF p.24, add Henselianity to Section 2.2;
the imported local-field compactness comparison already proves the full
local-field specialization without an additional premise.
The two-factor block is the published real-depth specialization of
Definition 7.3.3(1), printed p.247 / PDF p.278.

The proof first obtains closed representability of the actual nonzero
root subgroup using `subgroup_has_smooth_closed_representative`, with
smoothness of the connected reductive group and the splitness of the
actual maximal split torus. Closed immersion on rational points gives
`isClosed_rootGroup` in the same canonical ambient topology.
An open subgroup of the root group is closed there. Since the root group
is closed in `G(F)`, its filtration is closed in `G(F)` as well.
`localFieldAffineBoundedCompactness_proof` then converts the V 7
algebraic boundedness into ambient compactness. Compactness pulls back
along the closed root-group embedding to give compactness of
`filtrationOpenSubgroup`.

The doubled-root result splits according to whether `2a` is an actual
relative root. In that case it applies the filtration result; otherwise
the doubled-root filtration is the singleton identity. The root block
is the set product of its two compact factors, and multiplication is
continuous for the canonical topology. No subgroup or product
decomposition of the full point parahoric is asserted here. Boundedness
and openness of the full parahoric, including its centralizer factor,
remain separate obligations for the chamber compact-openness theorem.

The local instances have explicit module-specific names to avoid generated-name
collisions when these developments are imported together. Their types, bodies
and local scope are unchanged.

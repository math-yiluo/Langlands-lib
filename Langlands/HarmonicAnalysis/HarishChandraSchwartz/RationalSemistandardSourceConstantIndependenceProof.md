# Fixed-Levi independence of the actual source constants: proof

`Langlands.HarishChandraSchwartz.RationalSemistandard.sourceConstantParabolicIndependence`
proves the published proposition
`SourceConstantParabolicIndependenceStatement` of
`RationalSemistandardSourceConstants` for every connected reductive `G`.
The setting is unchanged: an arbitrary nonarchimedean local field `F` in
universe `u`, an affine `G` locally of finite type, and the fixed torus
`i`. Assume `i` is a maximal split torus, `nu` is generic, and the
common compact open `K` has
`BruhatTits.SpecialCompact.SpecialCompactProperties F i nu K`. Then for
any semistandard indices `p, q` with presentations `r, s` and
`p.levi = q.levi`, the actual constants `SourceConstants.gamma` and
`SourceConstants.c` of `r` and `s` at `K` agree. These constants are the
published `RationalDynamicSource.gamma` and
`RationalDynamicSource.plancherelConstant`, with their original Haar
measures normalized by `K` on the ambient group, the Levi and the
radicals. Neither constant is replaced and no premise is added.

This is the statement of Remark (3) of I.1 in J.-L. Waldspurger, *La
formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), printed pp.240–241
(PDF pp.6–7), registered as `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`. It
adds the independence of the product in the definition of `c(G|M)` on
p.241, which that definition presupposes. The case of two parabolics
that are neither equal nor opposite is included.

## Proof

1. *Same zero roots.* From `p.levi = q.levi` and the presentations'
   `levi_eq`, the dynamic centralizers of `r.hom` and `s.hom` are equal.
   The published `root_zero_imp_of_dynamicCentralizer_rationalPoints_le`
   (`CocharacterCentralizerPointDetection`), applied in both directions,
   shows that a relative root vanishes on `r.cocharacter` exactly when it
   vanishes on `s.cocharacter`.
2. *Limit stability of `K`.* `SpecialCompactProperties` contains
   `HasWeylRepresentatives i K` and `HasParabolicFactorization i nu K`.
   For every cocharacter `ξ` of the torus,
   `BruhatTits.SpecialCompact.mul_mem_iff_of_weylRepresentatives`
   (`SemistandardParabolicSplitting`) gives `m u ∈ K ↔ m ∈ K ∧ u ∈ K`
   on the Levi and radical points of `ξ`. The published
   `RationalDynamicSource.compact_split_iff_limit_stable` turns this into
   stability of `K` under the dynamic limit of `P(ξ)`.
3. *Gamma.* `RationalDynamicSource.gamma_eq_of_pairing_zero_iff`
   (`RationalSourceGammaCommonLevi`) gives equality of the two source
   gammas. It moves from one cocharacter toward the other in finitely
   many steps. Each step crosses the first sign change on the segment
   between them, which may lie on several root hyperplanes at once when
   ratios tie. The number of relative roots with opposite signs strictly
   decreases at each step. Each step is `gamma_eq_of_wall`
   (`RationalSourceGammaWall`): both
   gammas are evaluated as index products on one small compact open
   subgroup, using the published `gamma_eq_gammaIndex`,
   `gammaAuxiliarySubgroup_spec` and
   `StandardIntertwining.CommonLeviSplitting.exists_iwahoriCut`. The
   radical indices are then split along the parabolic `P(φ)` of the step
   (`SourceGammaIndexProduct.relIndex_mul_eq_of_wall`). The root and
   group comparisons use the published `relativeRootSignInclusions`,
   `dynamicCentralizer_le_of_pairing` and the shift lemmas
   `Dynamic.mem_unipotent_add_iff_of_mem_centralizer`.
4. *`c`.* `SourceConstants.c` unfolds to
   `γ⁻¹ * rankOneGammaProduct`. The gamma factors agree by step 3.
   `RationalDynamicSource.rankOneGammaProduct_eq_of_pairing_zero_iff`
   (`RationalPlancherelConstantCommonLevi`) gives equality of the
   rank-one products. Their index sets agree by the published
   `relativeRootNegation`. Each factor is moved between the two
   cocharacters by positive multiples (`rankOneGamma_zsmul`), by a shift
   inside the rank-one submodule, and, when the two parabolics are on
   opposite sides in the rank-one Levi, by the published
   `gamma_oppositeCocharacter` in the centralizer scheme
   (`leviGamma_eq_gamma_of_isClosedSubgroup`).

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

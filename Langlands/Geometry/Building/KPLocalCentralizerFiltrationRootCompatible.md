# Root compatibility of the torus filtration over `K = F^ur` (clause 2 of `QuasiSplitLocalTorusFiltrationStatement`)

This helper for clause 2 of `QuasiSplitLocalTorusFiltrationStatement` (KP Lemma 7.2.3
over `K`) is used, through `KPLocalCentralizerTorusFiltrationClauses`, by
`KPQuasiSplitLocalTorusFiltrationProof`. It imports the published statement
`KPLocalTorusRootCommutatorStatement`. The final proof supplies the helper's premise with
the published theorem `kpLocalTorusRootCommutator` from `KPLocalTorusRootCommutatorProof`.

Lean module: `Langlands.Geometry.Building.KPLocalCentralizerFiltrationRootCompatible`.
It uses the binders `B`, `hZ : IsTorus B.centralizer.Z` and the definitions
`centralizerTorusFiltration` and `centralizerTorusImage` of the Library module
`KPLocalMoyPrasadGroups`.

## Declarations

- `localTorusFiltration_le_localGeometricCharacterCongruence T hT hr`: for `r ≠ 0`, the
  published torus filtration `localTorusFiltration F T hT r` lies in the geometric congruence
  subgroup `localGeometricCharacterCongruence F T r`. Proof: at a nonzero depth the filtration
  is by definition the norm Iwahori subgroup intersected with this congruence subgroup.
- `B.conj_mem_filtration_of_mem_characterValuationKernel hz hu`: if `z` lies in
  `characterValuationKernel (valuation F) B.centralizer.Z` (the points with `ω(χ(z)) = 0`
  for every character `χ` of `Z` over `K`) and `u ∈ U_{a,x,s}`, then
  `j(z) u j(z)⁻¹ ∈ U_{a,x,s}`. Proof: `z` acts trivially on the apartment (axiom V6,
  `B.isOmegaCompatible.smul_eq_self`). Conjugation by its image in `N(K)` maps `U_{a,x,s}` to
  `U_{w(a), z·x, s}` (`B.apartment.conj_mem_filtration`), and the Weyl action of a centralizer
  point is trivial (`weylAction_centralizerToNormalizer`).
- `B.centralizerTorusFiltration_le_characterValuationKernel_valuation hZ r`: every `Z(K)_r`
  lies in that kernel. Proof: `centralizerTorusFiltration_le_characterValuationKernel` of `KPLocalMoyPrasadGroups`
  (for `fixedFieldValuation F`). The valuations `fixedFieldValuation F` and `valuation F` are
  equivalent (`valuation_isEquiv`), so they have the same kernel
  (`characterValuationKernel_eq_of_isEquiv`).
- `B.centralizerTorusImage_isRootCompatible_of_torusRoot hZ hroot`: assume
  `KPLocalTorusRootCommutatorStatement` (`hroot`). Then for every `x`, relative
  root `a`, `r s : ℝ≥0`, `z ∈ j(Z(K)_r) = B.centralizerTorusImage hZ r` and `u ∈ U_{a,x,s}`,
  `z u z⁻¹ u⁻¹ ∈ B.apartment.filtrationBlock x (fun _ => r + s) a`. This is clause 2 of
  `QuasiSplitLocalTorusFiltrationStatement` in the form of `ParahoricBuildingData.CentralizerFiltration.IsRootCompatible`, with `B` in
  place of `P`.

## Proof of the last declaration

Write `z = j(t)` with `t ∈ B.centralizerTorusFiltration hZ r`.

- `r = 0`: proved without `hroot`. `t` lies in the character valuation kernel, so `z u z⁻¹`
  lies in `U_{a,x,s}`. Hence `z u z⁻¹ u⁻¹ ∈ U_{a,x,s}`, and it equals
  `(z u z⁻¹ u⁻¹) · 1` in the block `U_{a,x,s} · U_{2a,x,s}`.
- `r > 0`: by the first declaration, `t` lies in
  `localGeometricCharacterCongruence F (B.centralizerTorus hZ) r`, and `hroot` gives the
  conclusion.

So clause 2 of `QuasiSplitLocalTorusFiltrationStatement` is proved at depth `0` and reduced to `KPLocalTorusRootCommutatorStatement`
at positive depth.

## Provenance

This is an internal consequence of the published torus filtration, its character-kernel
bound, apartment compatibility and the positive-depth torus/root statement. Root
compatibility is an additional derived property in the Library's KP §7.2 interface;
the literal Lemma 7.2.3 concerns commutator friendliness. The block is that of KP
Definition 7.3.3(1) (printed p.247). Source scope is documented in
`KPQuasiSplitLocalTorusFiltrationStatement.md` and `KPMoyPrasadFiltration.md`.

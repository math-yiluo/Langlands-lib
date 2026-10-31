# The relative Čech cohomology presheaves of a Chow datum are coherent (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow`. Its
declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow`.

## Statement

`solution`: let `R` be a noetherian ring, `πZ : Z ⟶ Spec R` proper and `D : ChowDatumProj πZ` a Chow datum
(`Def_AlgebraicGeometry_ProjSpace`): a proper `D.p : D.V' ⟶ Z` with a closed immersion
`D.ιN : D.V' ⟶ ℙ^{D.Nd}_R` over `Spec R`. Then for every `b` the relative Čech cohomology presheaf
`OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b` is coherent (`IsCoherent`,
`Def_AlgebraicGeometry_OrderedAffineCoverCech`): its value on every affine open `W` of `Z` is a finitely
generated `Γ(Z, W)`-module. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow` states this as
`AlgebraicGeometry.OModulePresheaf.Leray.isCoherent_relHPresheaf_chow` and proves it from `solution`.

## Proof outline

Section `Local` holds helpers shared with the companion `relHPresheaf_chow` modules: `res_res'` and
`res_refl'` (composition and identity of restrictions), `algebraOfHom_compat` and
`specMap_algebraMap_eq_fromSpec_comp` (the `R`-algebra structure on sections of an affine open), and
`isNoeth_of_proper` (a scheme proper over a noetherian ring is noetherian).

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray`, section `RelHPresheafChow`.

1. `lift_isClosedImm`: the map `D.V' ⟶ ℙ^{D.Nd}_R ×_{Spec R} Z` induced by `D.ιN` and `D.p` is a closed
   immersion.
2. `finite_relHPresheaf_obj_chow` fixes an affine open `W` of `Z`, with `A = Γ(Z, W)` noetherian (`Z` is
   noetherian by `isNoeth_of_proper`). Projective space over `A` is the base change of projective space over
   `R` (`ProjSpace.isPullback_map`, `Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map`), so `D.p⁻¹(W)`
   maps to `ℙ^{D.Nd}_A` by a morphism `ιW` that is proper and a monomorphism, hence a closed immersion. By
   `OModulePresheaf.cechFinite_unit_of_isClosedImmersion_proj`
   (`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj`) the structure
   sheaf of `D.p⁻¹(W)` has finitely generated Čech cohomology over `A` for the pulled-back standard cover.
3. The pieces of that cover are the opens `K'.inter τ ∩ D.p⁻¹(W)` (`hopen`, using
   `ProjSpace.map_preimage_basicOpen_X`, `Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X`),
   and the two `A`-module structures on their sections agree (`hact`). So the Čech complex of `D.p⁻¹(W)` is
   `A`-linearly isomorphic to the relative Čech complex `relAltC D.p πZ K' W` (`φC`, compatible with the
   differentials by `hcomm`), and the induced map on cohomology (`Φker`) is surjective. Hence
   `relAltH D.p πZ K' W b`, the value of `relHPresheaf` on `W`, is a finitely generated `A`-module.
4. `isCoherent_relHPresheaf_chow'` applies this to every affine open, and `solution` is that theorem.

As in FLT, the file removes some instances and simp lemmas for the rest of the file (`attribute [-instance]`
and `attribute [-simp]`).

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed
under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCover`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj`,
  `Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map` and
  `Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.

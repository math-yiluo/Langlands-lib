# The higher relative Čech cohomology of a Chow datum is supported off the isomorphism locus (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow`. Its
declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow`.

## Statement

`solution`: let `πZ : Z ⟶ Spec R` be separated and `D : ChowDatumProj πZ` a Chow datum
(`Def_AlgebraicGeometry_ProjSpace`), with `D.p : D.V' ⟶ Z` an isomorphism over the dense open `D.U`. Then for
every `b ≥ 1` the relative Čech cohomology presheaf
`OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b` is supported in the closed
complement of `D.U` (`SupportedIn`, `Def_AlgebraicGeometry_OrderedAffineCoverCech`): it vanishes on every
affine open of `Z` contained in `D.U`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow` states this as
`AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow` and proves it from `solution`.

## Proof outline

Section `Local` holds helpers shared with the companion `relHPresheaf_chow` modules: `res_res'` and
`res_refl'` (composition and identity of restrictions), `algebraOfHom_compat` and
`specMap_algebraMap_eq_fromSpec_comp` (the `R`-algebra structure on sections of an affine open), and
`isNoeth_of_proper` (a scheme proper over a noetherian ring is noetherian); they are not used by the main
argument here.

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray`, section `RelHPresheafChow`.

1. `preimage_isAffineOpen`: if `W ≤ D.U` is an affine open of `Z`, then `D.p⁻¹(W)` is affine, since over `D.U`
   the morphism `D.p` is an isomorphism (`D.hp_isoU`) and `D.p⁻¹(W)` is the pullback of `W`.
2. `supportedIn_relHPresheaf_chow'`: for such `W` and `b = b' + 1`, the Čech complex of the affine scheme
   `D.p⁻¹(W)` for its affine cover `restrictToPreimage` is exact in positive degrees
   (`Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen`), so its cohomology `HSucc b'` is
   trivial. By `OModulePresheaf.Leray.nonempty_relHPresheaf_obj_equiv_of_isAffineOpen`
   (`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen`)
   this is the value of `relHPresheaf … b` on `W`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed
under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCover`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`,
  `Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen` are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.

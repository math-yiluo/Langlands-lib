# The relative Čech cohomology presheaves of a Chow datum are quasi-coherent (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow`.

## Statement

`solution`: let `πZ : Z ⟶ Spec R` be separated and `D : ChowDatumProj πZ` a Chow datum
(`Def_AlgebraicGeometry_ProjSpace`): a proper `D.p : D.V' ⟶ Z` with a closed immersion
`D.ιN : D.V' ⟶ ℙ^{D.Nd}_R` over `Spec R`. Then for every `b` the relative Čech cohomology presheaf
`OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b` of `D.p`, computed with the
pullback of the standard affine cover of `ℙ^{D.Nd}_R`, is quasi-coherent (`IsQuasicoherent`,
`Def_AlgebraicGeometry_OrderedAffineCoverCech`). The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow` states this as
`AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow` and proves it from `solution`.

## Proof outline

Section `Local` holds helpers shared with the companion `relHPresheaf_chow` modules: `res_res'` and
`res_refl'` (composition and identity of restrictions), `algebraOfHom_compat` and
`specMap_algebraMap_eq_fromSpec_comp` (the `R`-algebra structure on sections of an affine open), and
`isNoeth_of_proper` (a scheme proper over a noetherian ring is noetherian).

The proof is `isQuasicoherent_relHPresheaf_chow'` in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray`.
Fix an affine open `U` of `Z` and `f ∈ Γ(Z, U)`, and write `K'` for the pulled-back cover.

1. Each piece `K'.inter τ ∩ D.p⁻¹(U)` of the relative Čech complex over `U` is affine
   (`Scheme.OrderedAffineCover.fiberAffineOpen`), and its intersection with `D.p⁻¹(D(f))` is the basic open of
   the pullback `g τ` of `f` (`hbo`). So the relative cochains over `D(f)` are the localization at `f` of
   those over `U`: every cochain over `D(f)` times a power of `f` comes from `U` (`hCsurj`; take the maximum
   of the exponents over the finitely many `τ`), and a cochain over `U` that restricts to `0` is killed by a
   power of `f` (`hCann`). The restriction `relRes` commutes with the differentials and is semilinear
   (`hres_d`, `hres_smul`).
2. The two conditions of `IsQuasicoherent` for the cohomology follow by the usual argument that localization
   is exact. For (a), lift a cocycle over `D(f)` to a cochain `y` over `U`; its coboundary restricts to `0`,
   so `fᴹ • y` is a cocycle lifting `f^{M+N}` times the class. For (b), if a cocycle over `U` becomes a
   coboundary over `D(f)`, lift the primitive and use `hCann` again to show that a power of `f` kills the
   class (in degree `0`, the cocycle itself is killed).

## Provenance and licence

This file is a port of
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCover` and
  `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.

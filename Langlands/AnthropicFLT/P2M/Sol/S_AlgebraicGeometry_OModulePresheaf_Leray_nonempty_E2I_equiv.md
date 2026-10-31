# The E₂ page of the Čech–Leray bicomplex is Čech cohomology of the relative cohomology presheaves (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv`.

## Statement

`solution`: for `p : V' ⟶ Z`, `πZ : Z ⟶ Spec R`, an ordered affine cover `K` of `Z` and an ordered affine
cover `K'` of `V'`, the `E₂` page `DoubleComplex.E₂I` of the Čech–Leray bicomplex
`OModulePresheaf.Leray.LerayDblCpx p πZ K K'` (vertical cohomology first;
`Def_AlgebraicGeometry_DoubleComplex`) is the Čech cohomology for `K` of the relative cohomology presheaves
`relHPresheaf p πZ K' b` (`Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`). There are `R`-linear
equivalences `E₂I (LerayDblCpx p πZ K K') 0 b ≃ₗ[R] (relHPresheaf p πZ K' b).H0 K` and
`E₂I (LerayDblCpx p πZ K K') (a + 1) b ≃ₗ[R] (relHPresheaf p πZ K' b).HSucc K a`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv` states this as
`AlgebraicGeometry.OModulePresheaf.Leray.nonempty_E2I_equiv` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray`. Through `biC_uncurry`, column `a` of
the bicomplex is the product over `σ : K.Idx a` of the relative Čech complexes `relAltC p πZ K' (K.inter σ)`
(`dV_uncurry`).

1. **Vertical cohomology.** `ker_dV_equiv` identifies the vertical cocycles at `(a, b)` with the product of
   the cocycles of `relAltd` over `K.inter σ`. `colB_eq_pi` matches the vertical coboundaries with the product
   of the coboundaries `relAltHB`. So `colH_iso` identifies the vertical cohomology `colH a b` with the Čech
   `a`-cochains of `relHPresheaf p πZ K' b` for `K` (using `Submodule.quotientPi`).
2. **Horizontal differential.** `colH_iso_intertwine` says that `colH_iso` carries the map `colHdH` induced by
   `dH` to the Čech differential of `relHPresheaf p πZ K' b` (via `dH_apply'` and `relResKer`).
3. **`E₂`.** Hence `ker_colHdH_equiv` identifies the cocycles, `E2I_zero_equiv` gives degree `0` (no
   coboundaries on either side) and `E2IB_map_eq` matches the coboundaries, giving `E2I_succ_equiv` in degree
   `a + 1`. `solution` packages these.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex` is
  renamed to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.

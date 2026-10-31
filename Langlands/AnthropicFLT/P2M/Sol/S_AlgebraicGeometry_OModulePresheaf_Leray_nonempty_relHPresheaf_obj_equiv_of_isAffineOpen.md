# Sections of the relative Čech cohomology presheaf over an affine open (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen`.

## Statement

`solution`: let `p : V' ⟶ Z` and `πZ : Z ⟶ Spec R` with `πZ` separated, `K'` an ordered affine cover of `V'`
and `U` an affine open of `Z`. Then the value on `U` of the relative Čech cohomology presheaf
`OModulePresheaf.Leray.relHPresheaf p πZ K' b` (`Def_AlgebraicGeometry_OModulePresheafLerayBicomplex`) is the
Čech cohomology of the structure sheaf of `p⁻¹(U)` for its ordered affine cover
`OModulePresheaf.Leray.restrictToPreimage p πZ K' hU` by the opens `K'.U i ∩ p⁻¹(U)`: there are `R`-linear
equivalences `(relHPresheaf p πZ K' 0).obj U ≃ₗ[R] (restrictToPreimage p πZ K' hU).H0 (p ≫ πZ)` and
`(relHPresheaf p πZ K' (b + 1)).obj U ≃ₗ[R] (restrictToPreimage p πZ K' hU).HSucc (p ≫ πZ) b`. The theorem
module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen`
states this as `AlgebraicGeometry.OModulePresheaf.Leray.nonempty_relHPresheaf_obj_equiv_of_isAffineOpen` and
proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray.CoverMatch`. Both sides are cohomology
of complexes of products of sections over the same opens `K'.inter τ ∩ p⁻¹(U)` (`inter_restrictToPreimage`),
so the proof matches them term by term.

1. `res_res` and `res_self` compose restrictions and remove trivial ones.
2. `cochainEquiv` identifies the relative cochains `relAltC p πZ K' U b` with the Čech cochains of
   `restrictToPreimage p πZ K' hU` by restricting along the equalities of opens, and `cochainEquiv_relAltd`
   says it intertwines `relAltd` with the Čech differential.
3. `kerEquiv` is the induced equivalence of cocycles (`kerEquiv_apply_coe`, `kerEquiv_symm_apply_coe`).
   `H0Equiv` is degree `0`, where both cohomologies are the cocycles. `relAltHB_map_kerEquiv` matches the
   coboundaries, giving `HSuccEquiv` in degree `b + 1`. `solution` packages these.

## Provenance and licence

This file is a port of
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
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

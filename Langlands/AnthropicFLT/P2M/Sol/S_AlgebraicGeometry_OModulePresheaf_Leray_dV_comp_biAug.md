# The augmentation of the Čech–Leray bicomplex commutes with the vertical differential (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug`.

## Statement

`solution`: for `p : V' ⟶ Z`, `πZ : Z ⟶ Spec R`, ordered affine covers `K` of `Z` and `K'` of `V'`, and
`b : ℕ`,
`(LerayDblCpx p πZ K K').dV 0 b ∘ₗ biAug p πZ K K' b = biAug p πZ K K' (b + 1) ∘ₗ (OModulePresheaf.unit (p ≫ πZ)).d K' b`.
So the augmentation `biAug` from the Čech complex of `𝒪_{V'}` for `K'` into the column `a = 0` of the
bicomplex (`Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`) is a map of complexes. The theorem
module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug` states this as
`AlgebraicGeometry.OModulePresheaf.Leray.dV_comp_biAug` and proves it from `solution`.

## Proof outline

The proof is `dV_comp_biAug'` in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray`. The auxiliary
lemmas `res_self'`, `unit_d_apply'` and `pullOpen_d_apply'` (as in the `Leray_rows_exact` module) write the
differentials as alternating sums of restrictions. Evaluating both sides at an index `(σ, τ)` with `dV_apply'`
and `unit_d_apply'` gives two alternating sums over the faces of `τ`. Their terms agree because both are
restrictions of the same section to the same open, by `biAug_apply` and `res_res`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug.lean` from the
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

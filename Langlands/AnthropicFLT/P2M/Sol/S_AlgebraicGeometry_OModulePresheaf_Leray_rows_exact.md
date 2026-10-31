# The rows of the Čech–Leray bicomplex are exact (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact`. Its declarations
live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact`.

## Statement

`solution`: let `p : V' ⟶ Z` and `πZ : Z ⟶ Spec R` with `πZ` and `p ≫ πZ` separated, `K` an ordered affine
cover of `Z` and `K'` one of `V'`. For the bicomplex `OModulePresheaf.Leray.LerayDblCpx p πZ K K'`
(`Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`), whose entry `(a, b)` is the product of the
sections of `𝒪_{V'}` over `K'.inter τ ∩ p⁻¹(K.inter σ)`, the horizontal (`K`-direction) differential `dH`
together with the augmentation `biAug` from the Čech cochains of `V'` for `K'` gives exact rows:

- `ker (dH (a + 1) b) ≤ range (dH a b)` for all `a, b`;
- `ker (dH 0 b) = range (biAug b)` for all `b`;
- `biAug b` is injective for all `b`.

The theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact` states this as
`AlgebraicGeometry.OModulePresheaf.Leray.rows_exact` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray`. Through `biC_uncurry'`, the row `b`
of the bicomplex is the product over `τ : K'.Idx b` of the Čech complexes of `pullOpen p πZ (K'.inter τ)` for
`K` (`dH_uncurry`).

1. **Auxiliary formulas** (section `Aux`). `res_self'` (restriction along `O ≤ O` is the identity),
   `unit_d_apply'` and `pullOpen_d_apply'` write the Čech differentials as alternating sums of restrictions.
2. **Row `τ` as a Čech complex of an affine scheme** (section `Rows`). `rowC_equiv` identifies the cochains of
   `pullOpen p πZ (K'.inter τ)` for `K` with the Čech cochains of the affine open `K'.inter τ` for its affine
   cover `rowCoverOf p πZ K K' τ` (both are products of sections over the same opens, by `inter_rowCoverOf`),
   and `rowC_comm` says the differentials correspond.
3. **Exactness.** The Čech complex of the structure sheaf of an affine open for an affine cover is exact and
   its augmentation is injective (`Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen`,
   `Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug`, `Scheme.OrderedAffineCoverOf.aug_injective`, from
   the corresponding theorem modules; `K'.inter τ` is affine by
   `Scheme.OrderedAffineCover.isAffineOpen_inter`). Applying this to every `τ` and reassembling with
   `biC_uncurry'` gives `ker_dH_succ_le_range_dH`, `ker_dH_zero_eq_range_biAug` (with `hbridge` matching
   `biAug` and the augmentation of each row) and `biAug_injective`. `solution` is the conjunction of the
   three.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`,
  `Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen`,
  `Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug` and
  `Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.

# The total cohomology of the Čech–Leray bicomplex is the Čech cohomology of the source (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv`.

## Statement

`solution`: let `p : V' ⟶ Z` and `πZ : Z ⟶ Spec R` with `πZ` and `p ≫ πZ` separated, `K` an ordered affine
cover of `Z` and `K'` one of `V'`. Then the cohomology of the total complex of the Čech–Leray bicomplex
`OModulePresheaf.Leray.LerayDblCpx p πZ K K'` (`DoubleComplex.HTot`, `Def_AlgebraicGeometry_DoubleComplex`) is
the Čech cohomology of `𝒪_{V'}` for `K'`: there are `R`-linear equivalences
`DoubleComplex.HTot (LerayDblCpx p πZ K K') 0 ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).H0 K'` and, for every `n`,
`DoubleComplex.HTot (LerayDblCpx p πZ K K') (n + 1) ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n`. The
theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv` states this as
`AlgebraicGeometry.OModulePresheaf.Leray.nonempty_HTot_equiv` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.Leray.Stair`. It is the standard staircase
argument for a double complex with exact augmented rows.

1. **The edge map** (section `Edge`). `eK' n` sends a Čech `n`-cochain `y` of `𝒪_{V'}` to the total
   `n`-cochain that is `biAug y` in position `(0, n)` and zero elsewhere (`eK'_apply_zero`, `eK'_apply_pos`).
   `dTot_single_apply_succ` (section `Generic`) computes the total differential of a cochain concentrated in
   one position.
2. **A map of complexes** (section `Main`). The rows are exact by `OModulePresheaf.Leray.rows_exact`
   (`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact`), so `dH ∘ biAug = 0` (`dH_biAug`), and
   `biAug` commutes with the vertical differential by `OModulePresheaf.Leray.dV_comp_biAug`. Hence `eK'`
   commutes with the differentials (`eK'_chain`).
3. **Surjectivity on cohomology** (`stair_surj`). A total cocycle `c` of degree `n + 1` is cohomologous to
   `eK' y` for a Čech cocycle `y`. By induction on the largest column `P` where `c` is nonzero, the component
   of `c` in column `P` is a horizontal cocycle, hence a horizontal coboundary by row exactness, and
   subtracting the total coboundary of its preimage moves `c` one column to the left. In column `0`, row
   exactness at the augmentation gives `y` with `biAug y = c₀,ₙ₊₁`, and `y` is a cocycle because `biAug` is
   injective.
4. **Injectivity on cohomology** (`stair_inj`). If `eK' y = dTot bb`, the same descending induction on `bb`
   shows that `y` is a Čech coboundary.
5. **The equivalences.** `HeK'` is the map induced by `eK'` on cohomology in degree `n + 1`, and
   `HTotSuccEquiv` is its inverse, bijective by steps 3 and 4. `HTotZeroEquiv` treats degree `0` directly: a
   total `0`-cocycle is a single entry in position `(0, 0)` killed by `dH` and `dV`, hence `biAug y` for a
   unique Čech `0`-cocycle `y`. `solution` packages these.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_dV_comp_biAug` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.

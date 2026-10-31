# The total cohomology of the Čech–Leray bicomplex is the Čech cohomology of the source

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv`.

## Statement

`AlgebraicGeometry.OModulePresheaf.Leray.nonempty_HTot_equiv`: for `p : V' ⟶ Z`, `πZ : Z ⟶ Spec R` with `πZ`
and `p ≫ πZ` separated, and ordered affine covers `K` of `Z` and `K'` of `V'`, there are `R`-linear
equivalences
`DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0 ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).H0 K'`
and, for every `n`,
`DoubleComplex.HTot (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (n + 1) ≃ₗ[R] (OModulePresheaf.unit (p ≫ πZ)).HSucc K' n`:
the total cohomology of the Čech–Leray bicomplex is the Čech cohomology of `𝒪_{V'}` for `K'`.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.solution R _ V' Z p πZ _ _ K K'`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_HTot_equiv.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex` and the
  corresponding `P2M.Sol` module are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).

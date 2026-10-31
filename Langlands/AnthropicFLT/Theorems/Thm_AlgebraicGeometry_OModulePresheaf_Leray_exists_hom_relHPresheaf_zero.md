# The zeroth relative Čech cohomology presheaf is the direct image of the structure sheaf

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero`.

## Statement

`AlgebraicGeometry.OModulePresheaf.Leray.exists_hom_relHPresheaf_zero`: for `p : V' ⟶ Z`, `πZ : Z ⟶ Spec R`
and an ordered affine cover `K'` of `V'`, there is
`φ : OModulePresheaf.Hom (OModulePresheaf.Leray.relHPresheaf p πZ K' 0) (OModulePresheaf.Leray.pullOpen p πZ ⊤)`
such that every `φ.app U` is bijective and, for every open `U` and every `0`-cocycle
`x : LinearMap.ker (OModulePresheaf.Leray.relAltd p πZ K' U 0)`,
`OModulePresheaf.Leray.relAug p πZ K' U (φ.app U (Submodule.Quotient.mk x)) = x.1`. So the zeroth relative
Čech cohomology presheaf is the direct image `U ↦ Γ(V', p⁻¹(U))` of the structure sheaf.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.solution R _ V' Z p πZ K'`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The
theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex` and the
  corresponding `P2M.Sol` module are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).

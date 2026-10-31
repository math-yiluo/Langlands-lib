# The higher relative Čech cohomology of a Chow datum is supported off the isomorphism locus

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow`.

## Statement

`AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow`: for a separated `πZ : Z ⟶ Spec R`, a
Chow datum `D : ChowDatumProj πZ` and `b ≥ 1`,
`(OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).SupportedIn ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩`:
the higher relative Čech cohomology presheaves of `D.p` vanish on affine opens contained in the open `D.U`
over which `D.p` is an isomorphism. As in FLT, the file removes some instances and simp lemmas for the rest of
the file (`attribute [-instance]` and `attribute [-simp]`); this does not affect the statement.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow.solution R _ Z πZ _ D b hb`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies. The
theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCover` and
  `Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex` and the corresponding `P2M.Sol` module are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).

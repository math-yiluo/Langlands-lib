# Finite Čech cohomology from a presentation of a graded module

Module `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses`.

## Statement

`ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses`: for a noetherian ring `R`, a graded module
`D : ProjSpaceCech.GradedModule R n`, a presentation `σ` of `D` and `i : ℕ`: if
`Module.Finite R (GradedModule.H σ.F i)` and `Module.Finite R (GradedModule.H σ.ker (i + 1))`, then
`Module.Finite R (GradedModule.H D i)`.

## Proof

`exact @_root_.P2MW.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.solution R _ _ n D σ i hF hK`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes
the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`,
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` and the corresponding `P2M.Sol` module are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied
  to the theorem's arguments in order (`_` for instance arguments).

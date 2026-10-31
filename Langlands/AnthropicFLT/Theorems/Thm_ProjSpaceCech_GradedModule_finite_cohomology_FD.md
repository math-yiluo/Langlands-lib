# The graded Čech cohomology of `S(d)` is finitely generated

Module `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_FD`.

## Statement

`ProjSpaceCech.GradedModule.finite_cohomology_FD`: for a commutative ring `R`, `n : ℕ`, `d₀ : ℤ` and
`i : ℕ`, the `R`-module `ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i`, the `i`-th
graded Čech cohomology of the free graded module `S(d₀)` over `S = R[X₀, …, Xₙ]`, is finitely generated
(`Module.Finite`).

## Proof

`exact @_root_.P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_FD.solution R _ n d₀ i`: the theorem is the
statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_ProjSpaceCech_GradedModule_finite_cohomology_FD.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`,
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` and the corresponding `P2M.Sol` module are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied
  to the theorem's arguments in order (`_` for instance arguments).

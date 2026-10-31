# Finite Čech cohomology from a presentation of a graded module (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses`. Its
declarations live in the namespace `P2MW.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses`.

## Statement

`solution`: let `R` be a noetherian ring, `D : ProjSpaceCech.GradedModule R n`, and `σ` a presentation of
`D`: a graded surjection from a finite sum `σ.F` of shifted free modules, with kernel `σ.ker`. If `Hⁱ(σ.F)` and
`H^{i+1}(σ.ker)` are finitely generated `R`-modules, then so is `Hⁱ(D)`. The theorem module
`Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses` states this as
`ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…ProjSpaceCech`.

1. **Cochain short exact sequence.** In each degree the induced maps of Čech cochains
   `C^i(σ.ker) → C^i(σ.F) → C^i(D)` form a short exact sequence. The second map is surjective
   (`GradedModule.piC_surjective`, lifting numerators through the presentation degree by degree), the first
   injective (`GradedModule.iotaC_injective`), and the sequence is exact in the middle
   (`GradedModule.altC_exact`).
2. **Connecting map.** As in the snake lemma (`GradedModule.snake_data`, using the FLT theorem
   `ProjSpaceCech.GradedModule.d_sq`), there is an `R`-linear map
   `GradedModule.delta0 : ker (d_D)ⁱ → H^{i+1}(σ.ker)`. Its kernel lies in the image of the cocycles of
   `σ.F` (`GradedModule.ker_delta0_le`), and it vanishes on coboundaries
   (`GradedModule.delta0_vanish_on_bdry`), so it descends to `δ : Hⁱ(D) → H^{i+1}(σ.ker)`.
3. **Finiteness** (`GradedModule.Presentation.finite_H_of_ses'`). `ker δ` lies in the image of
   `Hⁱ(σ.F) → Hⁱ(D)`, which is finitely generated, and `im δ` is a submodule of the noetherian module
   `H^{i+1}(σ.ker)`. Hence `Hⁱ(D)` is finitely generated (`Submodule.fg_of_fg_map_of_fg_inf_ker`).

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`,
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` and `Theorems.Thm_ProjSpaceCech_GradedModule_d_sq`
  are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect: each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same
  names, each `p2m_open "N"` becomes `open _root_.N`, and each `p2m_open_scoped "N" in` becomes
  `open scoped _root_.N in`. No declaration, statement or proof step changed.

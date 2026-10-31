# The graded Čech cohomology of a finite sum of twists `S(dₖ)` is finitely generated (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD`. Its only
declaration is `P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD.solution`.

## Statement

`solution`: for a commutative ring `R`, `n : ℕ`, a finite type `ι`, degrees `d₀ : ι → ℤ` and `i : ℕ`, the
`i`-th graded Čech cohomology of the product
`ProjSpaceCech.GradedModule.pi (fun k => ProjSpaceCech.GradedModule.FD R n (d₀ k))`, that is of the free graded
module `⊕ₖ S(d₀ k)` over `S = R[X₀, …, Xₙ]`, is a finitely generated `R`-module. The theorem module
`Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD` states this as
`ProjSpaceCech.GradedModule.finite_cohomology_pi_FD` and proves it from `solution`.

## Proof outline

Each factor has finitely generated cohomology by `ProjSpaceCech.GradedModule.finite_cohomology_FD`
(`Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_FD`), so the finite product of these
cohomology modules is finitely generated. `ProjSpaceCech.GradedModule.nonempty_HEquiv_pi`
(`Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi`) gives an `R`-linear equivalence `e` from the
cohomology of the product to that product, and `Module.Finite.equiv e.symm` concludes.

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`,
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule`,
  `Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi` and
  `Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_FD` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands.

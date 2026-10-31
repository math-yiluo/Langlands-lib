# The Čech differential of a graded module squares to zero (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_d_sq`. Its declarations live in the
namespace `P2MW.S_ProjSpaceCech_GradedModule_d_sq`.

## Statement

`solution`: for a commutative ring `R`, `n ∈ ℕ` and a graded module `D : ProjSpaceCech.GradedModule R n`
(`Def_AlgebraicGeometry_ProjSpaceCechGradedModule`), the combinatorial Čech differential satisfies
`d D (i + 1) ∘ d D i = 0` for every `i`. The theorem module `Theorems.Thm_ProjSpaceCech_GradedModule_d_sq`
states this as `ProjSpaceCech.GradedModule.d_sq` and proves it from `solution`.

## Proof outline

`GradedModule.d_sq'` (in the namespace `…ProjSpaceCech`): evaluate `d (d f)` at an index tuple `s`. It is a
double sum over `(a, b)` of `(−1)^{a+b}` times the image of `f` at the double face, mapped by two
restrictions `secIncl`, which compose to one (`GradedModule.secIncl_trans`). Split the pairs into
`{a ≤ b}` and its complement. The map `(a, b) ↦ (b + 1, a)` is a bijection between them, with equal double
faces (`Idx.succAbove_comp_succAbove`) and opposite signs, so the sum vanishes.
`GradedModule.range_d_le_ker` deduces `im d ⊆ ker d`.

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_GradedModule_d_sq.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and
is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` and
  `Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` are renamed to
  `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect: each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same
  names, each `p2m_open "N"` becomes `open _root_.N`, and each `p2m_open_scoped "N" in` becomes
  `open scoped _root_.N in`. No declaration, statement or proof step changed.

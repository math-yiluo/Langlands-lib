# The Čech differential for the twisting sheaves squares to zero (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_Twist_d_sq`. Its declarations live in the namespace
`P2MW.S_ProjSpaceCech_Twist_d_sq`.

## Statement

`solution`: for a commutative ring `R`, `n ∈ ℕ` and `d ∈ ℤ`, the combinatorial Čech differential of `𝒪(d)`
on `ℙⁿ_R` (`Def_AlgebraicGeometry_ProjSpaceCechTwist`) satisfies `Twist.d R n d (i + 1) ∘ Twist.d R n d i = 0`
for every `i`. The theorem module `Theorems.Thm_ProjSpaceCech_Twist_d_sq` states this as
`ProjSpaceCech.Twist.d_sq` and proves it from `solution`.

## Proof outline

`Twist.d_sq` (in the namespace `…ProjSpaceCech`): evaluate `d (d f)` at an index tuple `s`. It is a double
sum over `(a, b)` of `(−1)^{a+b}` times the image of `f` at the double face under two maps of finitely
supported functions induced by inclusions of monomial sets, which compose to one
(`Finsupp.lmapDomain_comp`). Split the pairs into `{a ≤ b}` and its complement. The map
`(a, b) ↦ (b + 1, a)` is a bijection between them, with equal double faces
(`Idx.succAbove_comp_succAbove`) and opposite signs, so the sum vanishes.

## Provenance and licence

This file is a port of `P2M/Sol/S_ProjSpaceCech_Twist_d_sq.lean` from the Anthropic Lean formalization of
Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed
under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect: each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same
  names, each `p2m_open "N"` becomes `open _root_.N`, and each `p2m_open_scoped "N" in` becomes
  `open scoped _root_.N in`. No declaration, statement or proof step changed.

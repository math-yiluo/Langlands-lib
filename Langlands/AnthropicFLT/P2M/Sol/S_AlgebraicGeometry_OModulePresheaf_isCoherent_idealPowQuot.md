# The graded pieces of the ideal filtration of a coherent sheaf are coherent (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R` with `V` locally noetherian, `I` an ideal sheaf
on `V`, and `F` a coherent presheaf of modules over `π`. Then for every `k` the graded piece
`I^k F / I^{k+1} F` (`OModulePresheaf.idealPowQuot π I F k`) is coherent. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot` states this as
`AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot` and proves it from `solution`.

## Proof outline

On an affine open `U`, the ring `Γ(V, U)` is noetherian and `F(U)` is finitely generated, hence a
noetherian module. Its submodule `I^k F(U)` is therefore finitely generated, and so is the quotient
`I^k F(U) / I^{k+1} F(U)`, as the image of the quotient map (`G4T.isCoherent_idealPowQuot`).

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isCoherent_idealPowQuot.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` is renamed
  to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file
  then raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.

# The cokernel of a morphism into a coherent presheaf of modules is coherent (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker`. Its declarations
live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker`.

## Statement

`solution`: for `π : V ⟶ Spec R`, presheaves of modules `F, G` over `π` and a morphism `φ : F ⟶ G`
(`OModulePresheaf.Hom`), if `G` is coherent then so is its cokernel `OModulePresheaf.coker φ`
(`Def_AlgebraicGeometry_OModulePresheafConstructions`; `IsCoherent` means finitely generated sections over
every affine open). The theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker`
states this as `AlgebraicGeometry.OModulePresheaf.isCoherent_coker` and proves it from `solution`.

## Proof outline

The proof is `isCoherent_coker` in the namespace `…AlgebraicGeometry.OModulePresheaf.G4T`. Over an affine open
`U`, the sections of `coker φ` are a quotient of the finitely generated `Γ(V, U)`-module `G.obj U`, via the
surjective projection of `imCokerSES φ`, so they are finitely generated (`Module.Finite.of_surjective`).

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false` (the file then
  raises the heartbeat limits further itself, as in FLT);
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. No declaration, statement or proof step
  changed.

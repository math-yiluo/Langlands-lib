# A power of the vanishing ideal kills a coherent sheaf supported on it (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R` with `V` locally noetherian, `Y` a closed subset
of `V`, and `F` a coherent, quasi-coherent presheaf of modules over `π` supported in `Y`. Then for every
affine open `U` there is `N` with `I_Y(U)^N · F(U) = 0`, where `I_Y` is the vanishing ideal of `Y`
(`idealPowSub π I_Y F N U = ⊥`). The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot` states this as
`AlgebraicGeometry.OModulePresheaf.exists_idealPowSub_eq_bot` and proves it from `solution`.

## Proof outline

The proof is in the namespace `…AlgebraicGeometry.OModulePresheaf.G4T`.

1. `support_vanishingIdeal`: the support of the vanishing ideal of `Y` is `Y`. Hence
   `basicOpen_disjoint_of_mem_vanishingIdeal`: for `f ∈ I_Y(U)`, the basic open `D(f)` is disjoint from
   `Y`, because the preimage of `D(f)` in the reduced subscheme of `Y` is the basic open of `0`.
2. For `f ∈ I_Y(U)`, `F(D(f))` is trivial since `F` is supported in `Y`. By quasi-coherence every
   `y ∈ F(U)` is killed by a power of `f`. As `F(U)` is finitely generated, one power of `f` kills
   `F(U)`. So `I_Y(U)` lies in the radical of the annihilator of `F(U)`.
3. `Γ(V, U)` is noetherian, so `I_Y(U)` is finitely generated and some power `I_Y(U)^N` lies in the
   annihilator (`Ideal.exists_pow_le_of_le_radical_of_fg`). Then `I_Y(U)^N · F(U) = 0`.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.lean` from the
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

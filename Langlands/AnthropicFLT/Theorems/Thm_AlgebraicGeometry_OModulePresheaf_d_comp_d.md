# The Čech differential of a presheaf of modules squares to zero

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d`.

## Statement

`AlgebraicGeometry.OModulePresheaf.d_comp_d`: let `R` be a commutative ring, `π : V ⟶ Spec R`, `F` a
presheaf of modules over `π` (`OModulePresheaf π`) and `K` an ordered affine cover of `V`. Then
`F.d K (i + 1) ∘ F.d K i = 0` for every `i`.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d.solution R _ V π F K i`: the theorem is
the statement of `solution` in
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_comp_d`, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` and
  `P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_comp_d` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d.solution` becomes
  `by exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d.solution R _ V π F K i`, which
  applies `solution` to the theorem's arguments in order (`_` for the instance argument).

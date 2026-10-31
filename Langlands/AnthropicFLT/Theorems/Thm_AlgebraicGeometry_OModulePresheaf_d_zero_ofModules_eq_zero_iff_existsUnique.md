# Čech 0-cocycles of a sheaf of modules are its global sections

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique`.

## Statement

`AlgebraicGeometry.OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique`: for `π : V ⟶ Spec R`,
`M : V.Modules`, an ordered affine cover `K` of `V` and `c : (OModulePresheaf.ofModules π M).cochain K 0`,
`(OModulePresheaf.ofModules π M).d K 0 c = 0 ↔ ∃! x : Γ(M, ⊤), ∀ s : K.Idx 0, c s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x`.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique.solution R _ V π M K c`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes the
proof.

## Provenance and licence

This file is a port of
`Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` and
  `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` and the corresponding `P2M.Sol` module are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied to
  the theorem's arguments in order (`_` for instance arguments).

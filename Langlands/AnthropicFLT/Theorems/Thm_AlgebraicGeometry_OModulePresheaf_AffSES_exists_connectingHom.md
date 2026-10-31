# Connecting maps for a short exact sequence of presheaves on affine opens

Module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom`.

## Statement

`AlgebraicGeometry.OModulePresheaf.AffSES.exists_connectingHom`: for a commutative ring `R`, a separated
`π : V ⟶ Spec R`, a short exact sequence `S : 0 → F₁ → F₂ → F₃ → 0` of presheaves of modules over `π` that
is exact on affine opens, and an ordered affine cover `K` of `V`, there are `R`-linear maps
`δ₀ : F₃.H0 K → F₁.HSucc K 0` and `δ i : F₃.HSucc K i → F₁.HSucc K (i + 1)` such that
`ker δ₀ ⊆ im (S.proj.H0Map K)`, `ker (δ i) ⊆ im (S.proj.HSuccMap K i)`,
`ker (S.inc.HSuccMap K 0) ⊆ im δ₀` and `ker (S.inc.HSuccMap K (i + 1)) ⊆ im (δ i)` for all `i`.

## Proof

`exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.solution R _ V π _ F₁ F₂ F₃ S K`:
the theorem is the statement of `solution` in the corresponding `P2M.Sol` module, whose Markdown describes
the proof.

## Provenance and licence

This file is a port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. The theorem name and statement are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafHom` and the
  corresponding `P2M.Sol` module are renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed, and the proof
  `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes `by exact @_root_.P2MW.S_….solution` applied
  to the theorem's arguments in order (`_` for instance arguments).

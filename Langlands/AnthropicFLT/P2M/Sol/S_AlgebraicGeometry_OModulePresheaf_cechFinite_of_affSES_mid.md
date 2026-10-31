# Finite Čech cohomology passes to the middle of a short exact sequence (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` separated, `K` an ordered affine cover of `V`,
and `S : 0 → F₁ → F₂ → F₃ → 0` a short exact sequence of presheaves of modules over `π`, exact on affine
opens. If `F₁` and `F₃` have finitely generated Čech cohomology for `K` (`CechFinite K`), so does `F₂`. The
theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_mid` and proves it from `solution`.

## Proof outline

1. `LES.cochain_ses` (with helpers `mem_comap_range_iff`, `d_d_apply`): the cochain maps form a short exact
   sequence in each degree, because `S` is exact on the affine intersections `K.inter s`.
2. Exactness in the middle of `Ȟⁱ(F₁) → Ȟⁱ(F₂) → Ȟⁱ(F₃)`: `ker ⊆ im` for the induced maps on cocycles in
   degree `0` (`ker_kerMap_le_range`) and on `HSucc` in higher degrees (`ker_HSuccMap_le_range`). A cocycle
   of `F₂` whose image is a coboundary is corrected by a lift of the bounding cochain, and the difference
   comes from a cocycle of `F₁`.
3. In each degree the outer terms are finitely generated, so the FLT theorem
   `Module.Finite.of_ker_le_range_of_isNoetherianRing` makes the middle term finitely generated.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafHom`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` and
  `Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.

# Transporting the induction hypothesis of the dévissage to a closed subscheme (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih`. Its
declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih`.

## Statement

`solution`: let `π : V ⟶ Spec R`, `K` an ordered affine cover of `V` and `Z₀` a closed subset of `V`, with
reduced subscheme `Z₀S` (the subscheme of `Scheme.IdealSheafData.vanishingIdeal Z₀`) and closed immersion
`ι : Z₀S ⟶ V`. Assume `ih`: every coherent, quasi-coherent presheaf of modules over `π` supported in a closed
set `Y' < Z₀` has `CechFinite K`. Then every coherent, quasi-coherent presheaf of modules `F` over `ι ≫ π`
supported in a closed subset `Y' < ⊤` of `Z₀S` has finite Čech cohomology for the preimage cover
`K.preimage ι`. The theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih`
states this as `AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih` and proves it from `solution`.

## Proof outline

The helpers are in the namespace `…AlgebraicGeometry.OModulePresheaf.Descend`, for a closed immersion
`i : Z ⟶ V` and a presheaf of modules `F` over `i ≫ π`.

1. `isCoherent_pushforward`: the pushforward `OModulePresheaf.pushforward π i F` is coherent if `F` is. Over
   an affine open `U`, `Γ(Z, i⁻¹U)` is a quotient of `Γ(V, U)` (`i` is a closed immersion), so a finitely
   generated `Γ(Z, i⁻¹U)`-module is finitely generated over `Γ(V, U)` (`Module.Finite.trans`).
2. `isQuasicoherent_pushforward`: the pushforward is quasi-coherent if `F` is, because `i⁻¹ D(f) = D(i^* f)`
   (`Scheme.preimage_basicOpen`) and powers of `f` act through `i^* f`.
3. `supportedIn_pushforward_image`: if `F` is supported in `Y'`, the pushforward is supported in the image
   `i(Y')`, which is closed.
4. `solution`: the image `Y''` of `Y'` in `V` is strictly smaller than `Z₀` (`i` is injective with image `Z₀`,
   and `Y' ≠ ⊤`). So `ih` applies to the pushforward of `F`, and `OModulePresheaf.cechFinite_pushforward_iff`
   transfers finiteness back to `F` and the preimage cover.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names.
  Each `p2m_open` becomes an `open` of the same namespaces, written with `_root_.` where needed and omitting a
  `P2MW`-prefixed namespace that does not exist yet at that point. These replacements change no declaration,
  statement or proof step.

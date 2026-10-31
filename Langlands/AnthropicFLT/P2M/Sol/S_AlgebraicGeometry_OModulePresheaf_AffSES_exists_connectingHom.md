# Connecting maps for a short exact sequence of presheaves on affine opens (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom`.
Its declarations live in the namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R` separated, `K` an ordered affine cover of `V`,
and `S : 0 → F₁ → F₂ → F₃ → 0` a short exact sequence of presheaves of modules over `π` that is exact on
every affine open (`OModulePresheaf.AffSES`). Then there are `R`-linear connecting maps
`δ₀ : Ȟ⁰(K, F₃) → Ȟ¹(K, F₁)` and `δᵢ : Ȟ^{i+1}(K, F₃) → Ȟ^{i+2}(K, F₁)` (in the notation of the definitions,
`F₃.H0 K → F₁.HSucc K 0` and `F₃.HSucc K i → F₁.HSucc K (i + 1)`) such that the long sequence is exact at the
two places around each connecting map:

- `ker δ₀ ⊆ im (Ȟ⁰(F₂) → Ȟ⁰(F₃))` and `ker δᵢ ⊆ im (Ȟ^{i+1}(F₂) → Ȟ^{i+1}(F₃))`;
- `ker (Ȟ¹(F₁) → Ȟ¹(F₂)) ⊆ im δ₀` and `ker (Ȟ^{i+2}(F₁) → Ȟ^{i+2}(F₂)) ⊆ im δᵢ`.

The theorem module `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom` states this
as `AlgebraicGeometry.OModulePresheaf.AffSES.exists_connectingHom` and proves it from `solution`.

## Proof outline

The proof is the snake lemma for the Čech complexes, in the namespace `…AlgebraicGeometry.OModulePresheaf.LES`.

1. `cochain_ses`: since `π` is separated, every intersection `K.inter s` is affine. So in each degree the
   cochain maps form a short exact sequence `0 → C^i(F₁) → C^i(F₂) → C^i(F₃) → 0`.
2. `snake_data`: for a cocycle `z` of `F₃` choose a lift `f₀` to `F₂`. Then `d f₀` comes from a cocycle
   `k₀` of `F₁`, using `d ∘ d = 0` (`d_d_apply`, from the FLT theorem `OModulePresheaf.d_comp_d`). Another
   lift `f` changes `k₀` only by a coboundary.
3. `delta0` sends `z` to the class of `k₀` (`delta0_spec`). It is `R`-linear because the choices are
   unique up to coboundaries. It kills coboundaries (`delta0_eq_zero_of_mem_range`), so it descends to
   `delta` on `HSucc`. The degree-zero map `δ₀` is `delta0` at degree `0`.
4. Exactness: if `δ z = 0`, adjusting the lift by the preimage of the coboundary gives a cocycle of `F₂`
   mapping to `z` (`ker_delta0_le_range`, `ker_delta_le_range`). If a class of `F₁` dies in `F₂`, the
   witnessing cochain of `F₂` projects to a cocycle of `F₃` whose connecting image is that class
   (`ker_HSuccMap_zero_le_range_delta0`, `ker_HSuccMap_succ_le_range_delta`). `mem_comap_range_iff`
   unfolds membership in the coboundaries.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.lean` from
the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafHom` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed and its commands are replaced by standard Lean
  commands with the same effect. Each `p2m_open` becomes an `open` of the same namespaces, written with
  `_root_.` where needed and omitting a `P2MW`-prefixed namespace that does not exist yet at that point.
  Each `p2m_export "N" "…"` becomes `export _root_.N (…)` with the same names. No declaration, statement
  or proof step changed.

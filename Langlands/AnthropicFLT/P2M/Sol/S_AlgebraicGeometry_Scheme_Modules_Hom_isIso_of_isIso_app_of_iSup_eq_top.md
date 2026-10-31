# A morphism of sheaves of modules that is an isomorphism locally is an isomorphism

`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top` proves the theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top.solution`. Its statement is that of `AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_isIso_app_of_iSup_eq_top`, which `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top` states under its FLT name.

## Statement

Let `X` be a scheme, `φ : M ⟶ N` a morphism of sheaves of modules on `X`
and `U : ι → X.Opens` a family of opens with `⨆ i, U i = ⊤` (the index type
`ι` lives in an arbitrary universe). If, for every `i` and every open
`V ≤ U i`, the component `φ.app V` is an isomorphism, then `φ` is an
isomorphism.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

View `M` and `N` as sheaves of abelian groups on `X` and `φ` as a morphism
`ψ` between them. By `Sheaf.isLocallyBijective_iff_isIso` it suffices that
`ψ` is locally injective and locally surjective. Every point `p` lies in
some `U i`. For local injectivity, if two sections `x`, `y` over `W` have
the same image, restrict them to `W ⊓ U i`: there `φ` is bijective, and by
naturality the restrictions of `x` and `y` have equal images, so they are
equal. For local surjectivity, a section `s` of `N` over `W` restricts on
`W ⊓ U i` to the image of a section of `M`, by bijectivity of
`φ.app (W ⊓ U i)`. Hence `ψ` is an isomorphism of sheaves, so every
component of the underlying morphism of presheaves is an isomorphism, and
`Scheme.Modules.Hom.isIso_iff_isIso_app` concludes.

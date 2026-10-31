# Pullback of sheaves of modules along a morphism of schemes is monoidal

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal`, in namespace
`AlgebraicGeometry.Scheme.Modules`. All schemes live in a fixed universe `u`; `f : X ⟶ Y` is a morphism
of schemes.

## Definitions and results

- Instances `preservesBinaryProducts_opensMap`, `preservesTerminal_opensMap` and
  `preservesFiniteProducts_opensMap`: the preimage functor `Opens.map f.base` on open sets preserves
  binary products (intersections), the terminal object (`⊤`) and hence finite products.
- `pullback₀ f : Y.PresheafOfModules ⥤ X.PresheafOfModules` is the pullback of presheaves of modules
  along `f` (an `example` checks that it is Mathlib's `PresheafOfModules.pullback` for `f`). The instance
  `pullback₀_monoidal` makes it monoidal, by `PresheafOfModules.PullbackMonoidal.pullback_monoidal`
  (`Def_PresheafOfModules_PullbackMonoidal`), since `Opens.map f.base` preserves finite products.
- Instance `sheafify_isLocalization'`: sheafification `Y.PresheafOfModules ⥤ Y.Modules` is a
  localization at the sheafification-local morphisms. The `Localization.Lifting` instance says that
  sheafification on `X` after `pullback₀ f` is the lift of `Modules.pullback f` through sheafification
  on `Y`.
- Instance `pullback_monoidal`: the pullback functor `Modules.pullback f : Y.Modules ⥤ X.Modules` of
  sheaves of modules is a monoidal functor, transported through the localization
  (`Localization.Monoidal.functorMonoidalOfComp`).
- `pullbackTensorObjIso f L M : f^*(L ⊗ M) ≅ f^*L ⊗ f^*M` and
  `pullbackTensorUnitObjIso f : f^* 𝒪_Y ≅ 𝒪_X` are the resulting isomorphisms.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ModulesPullbackMonoidal.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_PresheafOfModules_InternalHom`,
  `Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`,
  `Definitions.Def_SheafOfModules_Monoidal` and `Definitions.Def_PresheafOfModules_PullbackMonoidal` are
  renamed to the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

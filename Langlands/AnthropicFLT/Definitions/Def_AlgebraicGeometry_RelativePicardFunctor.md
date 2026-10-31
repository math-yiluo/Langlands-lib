# Invertible sheaves and the rigidified relative Picard presheaf

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, in namespace
`AlgebraicGeometry`. Schemes and rings live in a fixed universe `u`. `SchemeHomOver g f` is the type of
morphisms over a base from `Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`.

## Definitions and results

**Invertible sheaves.**

- `Scheme.Modules.IsInvertible M`, for a sheaf of modules `M` on a scheme `X`, means that every point of
  `X` has an open neighbourhood `U` on which `M` is isomorphic to the structure sheaf (the pullback of
  `M` along `U ⟶ X` is isomorphic to the unit sheaf of `U`). So `M` is locally free of rank one.
- Instance `Scheme.Hom.opensMapFinal`: for a morphism of schemes `f`, the preimage functor on opens is
  final.
- `Scheme.Modules.pullbackUnitIso f : f^* 𝒪_Y ≅ 𝒪_X`.
- `Scheme.Modules.isInvertible_unit`: the structure sheaf is invertible.
  `Scheme.Modules.IsInvertible.pullback`: pullbacks of invertible sheaves are invertible.

**Rigidified line bundles.** Fix `c : C ⟶ Spec R` with an `R`-point (section) `ε` of `C`. For
`t : T ⟶ Spec R`, write `C_T = C ×_R T`.

- `RelPicard.baseChangeSnd c s : C_{T'} ⟶ C_T` is the base change of a morphism `s : T' ⟶ T` over
  `Spec R`, and `RelPicard.rigSection c t ε : T ⟶ C_T` is the section induced by `ε`. `postComp`
  composes morphisms over `Spec R`, and the lemmas `baseChangeSnd_id`, `baseChangeSnd_comp` and
  `rigSection_baseChangeSnd` give functoriality and compatibility with the section.
- A `RigidifiedLineBundle c ε t` is an invertible sheaf `L` on `C_T` together with the existence of an
  isomorphism between its pullback along the section `rigSection c t ε` and the structure sheaf of `T`.
  Only the existence of the rigidification is recorded (`Nonempty`), not a chosen one.
  `RigidifiedLineBundle.unit t` is the structure sheaf (an `Inhabited` instance).
- `pullbackAlong M ψ` pulls a rigidified line bundle back along `ψ : T' ⟶ T` over `Spec R`.
- The `setoid` on `RigidifiedLineBundle c ε t` identifies `M` and `M'` when their sheaves `L` are
  isomorphic, as sheaves of modules on `C_T` (not necessarily compatibly with rigidifications).
  `pullbackAlong_congr` says pullback respects this relation, `Classes c ε t` is the quotient, and
  `classesMap ψ` is the induced map `Classes c ε t → Classes c ε t'`.
- `RelPicard.relPicardPresheaf c ε` is the presheaf on schemes over `Spec R` sending `T` to
  `Classes c ε t`, with the pullback maps. This is the rigidified relative Picard presheaf
  `T ↦ Pic(C_T)` restricted to classes of line bundles trivial along the section.
  `relPicardPresheaf.unitClass c ε X` is the class of the structure sheaf.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` is
  renamed to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

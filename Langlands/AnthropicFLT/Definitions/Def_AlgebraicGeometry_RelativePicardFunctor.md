# Invertible sheaves and the rigidified relative Picard presheaf

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor`, in namespace
`AlgebraicGeometry`. Schemes and rings live in a fixed universe `u`. `SchemeHomOver g f` is the type of
morphisms over a base from `Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`.

## Definitions and results

**Invertible sheaves.**

- `Scheme.Modules.IsInvertibleFLT M`, for a sheaf of modules `M` on a scheme `X`, means that every point of
  `X` has an open neighbourhood `U` on which `M` is isomorphic to the structure sheaf (the pullback of
  `M` along `U ⟶ X` is isomorphic to the unit sheaf of `U`). So `M` is locally free of rank one.
- Instance `Scheme.Hom.opensMapFinal`: for a morphism of schemes `f`, the preimage functor on opens is
  final.
- `Scheme.Modules.pullbackUnitIso f : f^* 𝒪_Y ≅ 𝒪_X`.
- `Scheme.Modules.isInvertible_unit`: the structure sheaf is invertible.
  `Scheme.Modules.IsInvertible.pullbackFLT`: pullbacks of invertible sheaves are invertible.

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
third-party notice applies. Declaration names and namespaces are FLT's, apart from the renames described under “Names changed by the Library” below. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` is
  renamed to `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- it declares `AlgebraicGeometry.Scheme.Modules.IsInvertibleFLT` (FLT `AlgebraicGeometry.Scheme.Modules.IsInvertible`), `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullbackFLT` (FLT `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback`);
- applications in dot notation on a hypothesis `h : Scheme.Modules.IsInvertibleFLT L` of lemmas of the name space `Scheme.Modules.IsInvertible` are written out (`h.pullback f` becomes `Scheme.Modules.IsInvertible.pullbackFLT (hL := h) f`): dot notation looks in the name space `IsInvertibleFLT`, and these lemmas stay in `IsInvertible`; the argument filled is the one dot notation filled.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are. The Lean file also imports `Langlands.MathlibBase` where FLT imports `Mathlib` (see `Langlands/MathlibBase.md`).

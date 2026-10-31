# The closed symmetric monoidal structure on sheaves of modules over a sheaf of commutative rings

Module `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal`, in namespaces `SheafOfModules`
and `AlgebraicGeometry`. All categories live in a fixed universe `u`.

## Definitions and results

Let `C` be a category with a Grothendieck topology `J` (with `J.WEqualsLocallyBijective` and weak
sheafification for abelian groups), and let `𝒪 : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings
whose underlying presheaf of rings is a sheaf (`h𝒪`).

- `ringSheaf 𝒪 h𝒪` is that sheaf of rings, and `PMod 𝒪` the category of presheaves of modules over
  `𝒪`.
- `presheafW J 𝒪` is the class of morphisms of presheaves of modules that become isomorphisms after
  sheafification of the underlying presheaves of abelian groups. `presheafW_isMonoidal` (theorem) says
  that this class is monoidal, by the FLT theorem
  `PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`.
- `sheafifyFunctor 𝒪 h𝒪 : PMod 𝒪 ⥤ SheafOfModules (ringSheaf 𝒪 h𝒪)` is sheafification, `toPMod` the
  forgetful functor back, and `sheafifyAdj` the sheafification adjunction. `toPMod` is fully faithful
  (instances), and sheafification is a localization at `presheafW J 𝒪` (instance).
  `sheafifyCounitIso` is the counit isomorphism `sheafify (toPMod M) ≅ M`, and `sheafifyUnitIso`
  identifies the sheafification of the monoidal unit of `PMod 𝒪` with the unit sheaf of modules.
- The instances `monoidalCategory` and `symmetricCategory` equip `SheafOfModules (ringSheaf 𝒪 h𝒪)` with
  the symmetric monoidal structure transported from presheaves through the localization
  (`LocalizedMonoidal`), so the tensor product of sheaves of modules is the sheafified presheaf tensor
  product. `sheafifyFunctor_monoidal` makes sheafification a monoidal functor, `tensorUnit_eq` says the
  monoidal unit is the unit sheaf `unit`, and `monoidalClosed` gives the closed structure (internal
  Hom) through the reflective adjunction (`Monoidal.Reflective.monoidalClosed`).
- `tensorIsoSheafify L M : sheafify (L ⊗ M as presheaves) ≅ L ⊗ M`.

For a scheme `X`:

- instances give `X.PresheafOfModules` its monoidal, symmetric and closed structures from presheaves of
  modules, and `X.Modules` its monoidal, symmetric and closed structures from the above;
- `Scheme.Modules.tensor L M = L ⊗ M`, and `Scheme.Modules.dual L` is the internal Hom
  `(ihom L).obj 𝟙` from `L` to the unit, the dual sheaf `L^∨ = ℋom(L, 𝒪_X)`;
- `Scheme.Modules.tensorUnit_eq`: the monoidal unit of `X.Modules` is the structure sheaf;
- `Scheme.Modules.sheafify X` is sheafification `X.PresheafOfModules ⥤ X.Modules` (a monoidal functor,
  instance), and `Scheme.Modules.tensorIsoSheafify` is `tensorIsoSheafify` for `X`.

## Provenance and licence

This file is a port of `Definitions/Def_SheafOfModules_Monoidal.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_PresheafOfModules_InternalHom` and
  `Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf` are renamed to
  `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom` and
  `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

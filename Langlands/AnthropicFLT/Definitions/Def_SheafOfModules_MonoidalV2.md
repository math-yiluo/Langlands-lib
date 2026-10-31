# Private copies of two results on internal Homs and sheafification of presheaves of modules

Module `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2`.

## Contents

Every declaration in this file is `private`, so the module adds no public declaration. FLT generated it
by inlining two theorem files into a definitions module. The file imports
`Def_PresheafOfModules_InternalHom` and `Def_SheafOfModules_Monoidal`, so modules importing it also
receive those two modules. The private content is:

- **Internal Hom of a sheaf is a sheaf** (`PresheafOfModules.isSheaf_ihomObj_loc`, private theorem). Let
  `R : Cᵒᵖ ⥤ CommRingCat`, `F`, `N` presheaves of modules over `R`, and `J` a Grothendieck topology on
  `C`. If the underlying presheaf of abelian groups of `N` is a `J`-sheaf, then so is that of the
  internal Hom `ihomObj F N`. The proof identifies the internal Hom with the subpresheaf of
  `presheafHom F N` consisting of the `R`-linear families (`linearSub`, via `toPresheafHom`,
  `ofPresheafHom`, `equivLinearSub`, `isoLinearSub`). It shows that `R`-linearity is a local condition
  when `N` is separated (`linearSub_local`), and concludes because `presheafHom F N` is a sheaf.
- **The sheafification-local morphisms form a monoidal class**
  (`PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf_loc`, private theorem). Let
  `α : 𝒪 ⋙ forget₂ ⟶ R.obj` be a locally bijective morphism from a presheaf of commutative rings to a
  sheaf of rings. Then the class `W` of morphisms of presheaves of modules over `𝒪` whose underlying
  presheaves of abelian groups become isomorphisms after sheafification is stable under whiskering on
  either side. The proof identifies `W` with the morphisms inverted by sheafification (`W_eq`). The
  sheafification unit is an isomorphism at sheaves (`isIso_unit_app_of_isSheaf`). By the first result
  and the reflective-localization criterion `Monoidal.Reflective.isIso_tfae`, sheafification inverts
  `η_d ▷ d'` (`isIso_shf_map_unit_whiskerRight`). A two-out-of-three argument then gives stability under
  right whiskering (`W_whiskerRight`), and the braiding gives left whiskering.

These are FLT's inlined copies of the theorems `PresheafOfModules.isSheaf_ihomObj` and
`PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`, which are also ported as separate FLT
theorem modules.

## Provenance and licence

This file is a port of `Definitions/Def_SheafOfModules_MonoidalV2.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_PresheafOfModules_InternalHom` and
  `Definitions.Def_SheafOfModules_Monoidal` are renamed to `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- one proof step is adapted to the pinned Mathlib (FLT pins Lean 4.33.1 and Mathlib `db584cd6`; this
  project pins Lean 4.34.0 and Mathlib `5ed29652`, where the list in `Monoidal.Reflective.isIso_tfae`
  is indexed differently, so `.out 0 2` becomes `.out 1 3`). The diff against the FLT file (after the
  import rename and option insertion) is:

```diff
--- FLT/Definitions/Def_SheafOfModules_MonoidalV2.lean (imports rewritten, options inserted)
+++ port
@@ -176,3 +176,3 @@
     IsIso ((shf 𝒪 R α).map (((adj 𝒪 R α).unit.app d) ▷ d')) := by
-  have h := (Monoidal.Reflective.isIso_tfae (adj 𝒪 R α)).out 0 2
+  have h := (Monoidal.Reflective.isIso_tfae (adj 𝒪 R α)).out 1 3
   refine (h.mp ?_) d d'
```

The line numbers refer to the file without the attribution header.

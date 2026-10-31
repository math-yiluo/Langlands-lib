# Monoidality of restriction of scalars, pushforward and pullback of presheaves of modules

Module `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_PullbackMonoidal`, in namespaces
`PresheafOfModules` and `CategoryTheory.Limits`.

## Definitions and results

Presheaves of modules are taken over presheaves of commutative rings, through the forgetful functor to
rings.

**Restriction of scalars.** For a morphism `φ : S ⟶ R` of presheaves of commutative rings on `C`:

- `ringCatHom φ` is `φ` as a morphism of presheaves of rings, and `restrictScalarsAt φ U` is restriction
  of scalars `ModuleCat R(U) ⥤ ModuleCat S(U)`;
- `restrictScalarsε φ` and `restrictScalarsμ φ M N` are the unit and tensor comparison maps of
  restriction of scalars along `φ`, built objectwise, and the instance `restrictScalars_laxMonoidal`
  makes restriction of scalars a lax monoidal functor.

**Pushforward and pullback.** For a functor `F : C ⥤ D` and `φ : S ⟶ F.op ⋙ R`:

- `pushforward_laxMonoidal`: the pushforward of presheaves of modules along `(F, φ)` is lax monoidal,
  being restriction of scalars after the plain pushforward;
- `pullback_oplaxMonoidal`: when the pushforward is a right adjoint, the pullback (its left adjoint) is
  oplax monoidal.

**Colimits and free modules.**

- `CategoryTheory.Limits.isIso_app_of_isColimit`: if two functors preserve a colimit and a natural
  transformation between them has isomorphism components at every object of the diagram, then its
  component at the colimit point is an isomorphism.
- `freeObj_map_freeMk` computes the restriction maps of the free presheaf of modules on a presheaf of
  sets on generators. `freeεIso` identifies the monoidal unit with the free module on the terminal
  presheaf of sets, and `freeμIso F G : free F ⊗ free G ≅ free (F ⊗ G)` (`freeμIso_hom_app`,
  `freeεIso_hom_app`). The instance `free_monoidal` makes the free-module functor from presheaves of sets
  a monoidal functor.

**The pullback is monoidal** (namespace `PullbackMonoidal`). Let `C`, `D` be small categories with
finite products, `F : C ⥤ D` a functor preserving finite products, and `φ : S ⟶ F.op ⋙ R`. Write `pf`
and `pb` for the pushforward and pullback, `adj : pb ⊣ pf`, and `gS U`, `gR V` for the free presheaves of
modules on the representable presheaves `yoneda U`, `yoneda V`.

- `h₂`, `u₂` and `e U : pb (gS U) ≅ gR (F U)`: the pullback of a free representable module is the free
  representable module on the image object (via corepresentability of `pf ⋙ coyoneda (gS U)`;
  helper lemmas `freeYonedaEquiv_apply'`, `gS_map_freeMk`, `gR_map_freeMk`, `free_map_app_freeMk`,
  `freeμIso_inv_app_freeMk`, `tensorHom_app_tmul`, `u₂_app_freeMk`, `unit_comp_map_e_hom`).
- `yonedaTensorIso U V : yoneda U ⊗ yoneda V ≅ yoneda (U ⨯ V)` and
  `tensorUnitIso E : 𝟙 ≅ yoneda (⊤_ E)` (`yonedaTensorIso_inv_app_apply`). From these, `j`, `j₀`, `r`
  and `r₀` identify tensor products and the unit of free representable modules over `C` and over `D`.
- `δ_gS_comp` expresses the oplax comparison `δ` of `pb` at `(gS U, gS V)` through these isomorphisms
  (computed on generators in `pf_μ_app_tmul`, `keyL`, `keyR`, `key_δ`), so `δ` is an isomorphism there
  (`isIso_δ_gS`).
- `isIso_app_of_freeYoneda`: a natural transformation between colimit-preserving functors out of
  presheaves of modules that is an isomorphism on every free representable module is an isomorphism,
  because every presheaf of modules is a cokernel of coproducts of free representable ones. With the
  instance that `pb` preserves colimits, this gives `isIso_δ`: `δ` is an isomorphism for all `A`, `B`.
- `η_eq` (through `keyL₀`, `keyR₀`, `key_η`) and `isIso_η`: the unit comparison `η` of `pb` is an
  isomorphism.
- `pullback_monoidal`, and the instance `pullback_monoidal'` outside the namespace: under these
  hypotheses the pullback of presheaves of modules is a (strong) monoidal functor.

## Provenance and licence

This file is a port of `Definitions/Def_PresheafOfModules_PullbackMonoidal.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- proofs are adapted to the pinned Mathlib (FLT pins Lean 4.33.1 and Mathlib `db584cd6`; this project
  pins Lean 4.34.0 and Mathlib `5ed29652`). There the presheaf monoidal lemmas `tensorObj_map_tmul`,
  `whiskerLeft_app`, `whiskerRight_app`, `associator_hom_app`, `leftUnitor_hom_app` and
  `rightUnitor_hom_app` live in the namespace `PresheafOfModulesOfCommRing`. The functor-category lemmas
  are named `CategoryTheory.Monoidal.*`. `ModuleCat.restrictScalars_μ_tmul` needs its ring map
  explicitly, and an `erw [PresheafOfModules.tensorHom_app]` is no longer needed. The diff against the
  FLT file (after the option insertion) is:

```diff
--- FLT/Definitions/Def_PresheafOfModules_PullbackMonoidal.lean (imports rewritten, options inserted)
+++ port
@@ -46,5 +46,5 @@
     dsimp
-    erw [Monoidal.tensorObj_map_tmul]
+    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
     erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
-    erw [Monoidal.tensorObj_map_tmul]
+    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
     rfl
@@ -57,3 +57,3 @@
     ext1 U
-    simp only [comp_app, whiskerRight_app, restrictScalars_map_app]
+    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, restrictScalars_map_app]
     exact μ_natural_left (restrictScalarsAt φ U) (f.app U) (N.obj U)
@@ -61,3 +61,3 @@
     ext1 U
-    simp only [comp_app, whiskerLeft_app, restrictScalars_map_app]
+    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app]
     exact μ_natural_right (restrictScalarsAt φ U) (M.obj U) (f.app U)
@@ -65,4 +65,4 @@
     ext1 U
-    simp only [comp_app, whiskerRight_app, whiskerLeft_app, restrictScalars_map_app,
-      associator_hom_app]
+    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app,
+      PresheafOfModulesOfCommRing.associator_hom_app]
     exact associativity (restrictScalarsAt φ U) (M.obj U) (N.obj U) (P.obj U)
@@ -70,3 +70,3 @@
     ext1 U
-    simp only [comp_app, whiskerRight_app, restrictScalars_map_app, leftUnitor_hom_app]
+    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerRight_app, restrictScalars_map_app, PresheafOfModulesOfCommRing.leftUnitor_hom_app]
     exact left_unitality (restrictScalarsAt φ U) (M.obj U)
@@ -74,3 +74,3 @@
     ext1 U
-    simp only [comp_app, whiskerLeft_app, restrictScalars_map_app, rightUnitor_hom_app]
+    simp only [comp_app, PresheafOfModulesOfCommRing.whiskerLeft_app, restrictScalars_map_app, PresheafOfModulesOfCommRing.rightUnitor_hom_app]
     exact right_unitality (restrictScalarsAt φ U) (M.obj U)
@@ -168,3 +168,3 @@
     erw [ModuleCat.FreeMonoidal.μIso_inv_freeMk]
-    erw [Monoidal.tensorObj_map_tmul]
+    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
     erw [freeObj_map_freeMk, freeObj_map_freeMk, freeObj_map_freeMk]
@@ -185,4 +185,4 @@
         ext1 X
-        simp only [comp_app, whiskerRight_app, free_map_app, freeμIso_hom_app,
-          Monoidal.whiskerRight_app]
+        simp only [comp_app, CategoryTheory.Monoidal.whiskerRight_app, free_map_app, freeμIso_hom_app,
+          PresheafOfModulesOfCommRing.whiskerRight_app]
         exact μ_natural_left (ModuleCat.free (R.obj X)) (f.app X) (G.obj X)
@@ -190,4 +190,4 @@
         ext1 X
-        simp only [comp_app, whiskerLeft_app, free_map_app, freeμIso_hom_app,
-          Monoidal.whiskerLeft_app]
+        simp only [comp_app, CategoryTheory.Monoidal.whiskerLeft_app, free_map_app, freeμIso_hom_app,
+          PresheafOfModulesOfCommRing.whiskerLeft_app]
         exact μ_natural_right (ModuleCat.free (R.obj X)) (G.obj X) (f.app X)
@@ -195,4 +195,4 @@
         ext1 X
-        simp only [comp_app, whiskerRight_app, whiskerLeft_app, free_map_app, freeμIso_hom_app,
-          associator_hom_app, Monoidal.associator_hom_app]
+        simp only [comp_app, CategoryTheory.Monoidal.whiskerRight_app, CategoryTheory.Monoidal.whiskerLeft_app, free_map_app, freeμIso_hom_app,
+          CategoryTheory.Monoidal.associator_hom_app, PresheafOfModulesOfCommRing.associator_hom_app]
         exact associativity (ModuleCat.free (R.obj X)) (F.obj X) (G.obj X) (H.obj X)
@@ -200,4 +200,4 @@
         ext1 X
-        simp only [comp_app, whiskerRight_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
-          leftUnitor_hom_app, Monoidal.leftUnitor_hom_app]
+        simp only [comp_app, CategoryTheory.Monoidal.whiskerRight_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
+          CategoryTheory.Monoidal.leftUnitor_hom_app, PresheafOfModulesOfCommRing.leftUnitor_hom_app]
         exact left_unitality (ModuleCat.free (R.obj X)) (F.obj X)
@@ -205,4 +205,4 @@
         ext1 X
-        simp only [comp_app, whiskerLeft_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
-          rightUnitor_hom_app, Monoidal.rightUnitor_hom_app]
+        simp only [comp_app, CategoryTheory.Monoidal.whiskerLeft_app, free_map_app, freeμIso_hom_app, freeεIso_hom_app,
+          CategoryTheory.Monoidal.rightUnitor_hom_app, PresheafOfModulesOfCommRing.rightUnitor_hom_app]
         exact right_unitality (ModuleCat.free (R.obj X)) (F.obj X) }
@@ -283,3 +283,2 @@
       ((f ⊗ₘ g).app X).hom (m ⊗ₜ[T.obj X] n) = f.app X m ⊗ₜ[T.obj X] g.app X n := by
-  erw [PresheafOfModules.tensorHom_app]
   exact ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _
@@ -380,3 +379,3 @@
     Category.comp_id]
-  exact ModuleCat.restrictScalars_μ_tmul _ _ _ m n
+  exact ModuleCat.restrictScalars_μ_tmul (φ.app (op W)).hom _ _ m n
 
```

The line numbers refer to the file without the attribution header. The file imports only Mathlib, so its
imports are unchanged.

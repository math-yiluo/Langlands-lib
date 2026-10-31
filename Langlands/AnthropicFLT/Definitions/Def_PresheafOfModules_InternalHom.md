# The internal Hom of presheaves of modules over a presheaf of commutative rings

Module `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom`, in namespace
`PresheafOfModules`.

## Definitions and results

Let `C` be a category and `R : Cᵒᵖ ⥤ CommRingCat` a presheaf of commutative rings; `F`, `N` are
presheaves of modules over `R` (over the underlying presheaf of rings).

**Natural families.** For an object `X` of `Cᵒᵖ`:

- a `PiFamily F N X` assigns to each `f : X ⟶ Y` an `R(Y)`-linear map `F(Y) → N(Y)`;
- `IsNatural φ` means `N.map g (φ f x) = φ (f ≫ g) (F.map g x)` for all `f : X ⟶ Y`, `g : Y ⟶ Z`;
- `naturalFamilies F N X` is the additive subgroup of natural families. These are the sections of
  `ℋom(F, N)` over `X`: compatible families of linear maps on everything below `X`. It is an
  `R(X)`-module, `r` acting on the component at `f` by `R.map f r` (instances; lemmas `smul_app`,
  `add_app`, `zero_app`, `neg_app`, `sub_app`, `naturalFamilies_ext`, `naturality`, `congr_app`,
  `map_id_apply`).
- `restrict F N h`, for `h : X ⟶ X'`, sends a family `φ` to `f ↦ φ (h ≫ f)` (`restrict_app`), and
  `InternalHom.presheaf F N` is the resulting presheaf of abelian groups (`presheaf_map_apply`), with
  the `R(X)`-module structure on each value (instance).
- `postcomp F ψ X`, for `ψ : N ⟶ N'`, composes a family with `ψ` (`postcomp_app`).

**The internal Hom functor.**

- `ihomObj F N` is the presheaf of modules with values `naturalFamilies F N X` (`ihomObj_map_val`).
- `ihomMap F ψ : ihomObj F N ⟶ ihomObj F N'` is induced by `ψ` (`ihomMap_app_val`), and
  `ihomFunctor F` is the functor `N ↦ ihomObj F N` (`ihomFunctor_obj`, `ihomFunctor_map`).

**Tensor–Hom adjunction.** Now let `C` and `R` live in a single universe `u`, and `G` be a third
presheaf of modules.

- `InternalHom.curryFamily F θ y`, for `θ : F ⊗ G ⟶ N` and `y ∈ G(X)`, is the natural family
  `f ↦ (x ↦ θ (x ⊗ G.map f y))` (`curryFamily_app`), and `curry' F θ : G ⟶ ihomObj F N` collects these
  (`curry'_app_val`).
- `uncurryApp F κ X` is the linear map `F(X) ⊗ G(X) → N(X)`, `x ⊗ y ↦ (κ y) (𝟙 X) x`
  (`uncurryApp_tmul`), and `uncurry' F κ : F ⊗ G ⟶ N` is the resulting morphism (`uncurry'_app_tmul`;
  `tensorObj_map_tmul'` describes the restriction maps of `F ⊗ G` on pure tensors).
- `uncurry'_curry'` and `curry'_uncurry'`: the two constructions are mutually inverse.
- `tensorIhomAdj F` is the adjunction `F ⊗ – ⊣ ihomFunctor F`, and the instance `instMonoidalClosed`
  makes presheaves of modules over `R` a monoidal closed category.

## Provenance and licence

This file is a port of `Definitions/Def_PresheafOfModules_InternalHom.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- two proofs are adapted to the pinned Mathlib (FLT pins Lean 4.33.1 and Mathlib `db584cd6`; this
  project pins Lean 4.34.0 and Mathlib `5ed29652`). There the presheaf monoidal lemma
  `Monoidal.tensorObj_map_tmul` lives in the namespace `PresheafOfModulesOfCommRing`, and the rewrite
  with `PresheafOfModules.map_comp_apply` is tried in three forms and closed by `rfl`. The lemma
  `uncurryApp_tmul` holds by `rfl`, without `erw [ModuleCat.MonoidalCategory.tensorLift_tmul]`. The diff
  against the FLT file (after the option insertion) is:

```diff
--- FLT/Definitions/Def_PresheafOfModules_InternalHom.lean (imports rewritten, options inserted)
+++ port
@@ -207,4 +207,8 @@
     rw [← naturality_apply]
-    erw [Monoidal.tensorObj_map_tmul]
-    rw [← PresheafOfModules.map_comp_apply]⟩
+    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
+    first
+      | rw [PresheafOfModules.map_comp_apply]
+      | erw [PresheafOfModules.map_comp_apply]
+      | simp only [PresheafOfModules.map_comp_apply]
+    rfl⟩
 
@@ -271,4 +275,3 @@
     DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
-      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by
-  erw [ModuleCat.MonoidalCategory.tensorLift_tmul]
+      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := rfl
 
```

The line numbers refer to the file without the attribution header. The file imports only Mathlib, so its
imports are unchanged.

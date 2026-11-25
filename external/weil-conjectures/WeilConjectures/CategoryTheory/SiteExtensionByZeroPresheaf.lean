/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Extension by zero of abelian presheaves on a slice category

Source: Stacks Project, Modules on Sites, Lemma 03DI and Remark 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf).
-/

@[expose] public section

set_option autoImplicit false

universe u v w r

open CategoryTheory

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (W : C)

open Classical in
/-- The direct sum of the values at all arrows into `W`. Stacks Project, 03DI and 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
noncomputable def siteExtensionByZeroSection (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w})
    (V : Cᵒᵖ) : AddCommGrpCat.{max v w} :=
  AddCommGrpCat.of (DirectSum (V.unop ⟶ W)
    (fun φ => F.obj (Opposite.op (Over.mk φ))))

open Classical in
/-- Restriction maps the `φ` summand to the `a.unop ≫ φ` summand using `F.map`.
Stacks Project, 03DI and 03EJ (blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
noncomputable def siteExtensionByZeroRestrict (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w})
    {V V' : Cᵒᵖ} (a : V ⟶ V') :
    siteExtensionByZeroSection W F V ⟶ siteExtensionByZeroSection W F V' :=
  AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun φ : V.unop ⟶ W =>
    (DirectSum.of (fun ψ : V'.unop ⟶ W => F.obj (Opposite.op (Over.mk ψ)))
      (a.unop ≫ φ)).comp
        (F.map (Opposite.op (Over.homMk a.unop :
          Over.mk (a.unop ≫ φ) ⟶ Over.mk φ))).hom)

/-- Identity restriction: check each direct-sum injection, use `F.map_id`, and the
identity law in `C`. Stacks Project, 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
theorem siteExtensionByZeroRestrict_id (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}) (V : Cᵒᵖ) :
    siteExtensionByZeroRestrict W F (𝟙 V) = 𝟙 (siteExtensionByZeroSection W F V) := by
  classical
  apply AddCommGrpCat.hom_ext
  dsimp [siteExtensionByZeroRestrict, siteExtensionByZeroSection]
  apply DirectSum.addHom_ext
  intro i x
  simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  have h (j : V.unop ⟶ W) (hj : j = i)
      (f : Over.mk j ⟶ Over.mk i) (hf : f.left = 𝟙 V.unop) :
      DirectSum.of (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ))) j
        ((F.map f.op).hom x) =
      DirectSum.of (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ))) i x := by
    subst j
    have hf' : f = 𝟙 (Over.mk i) := Over.OverMorphism.ext hf
    simp [hf']
  exact h _ (Category.id_comp i) _ rfl

/-- Composition of restrictions: on each injection use `F.map_comp` and associativity
in `C`; direct-sum extensionality gives the equality. Stacks Project, 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
theorem siteExtensionByZeroRestrict_comp (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w})
    {V V' V'' : Cᵒᵖ} (a : V ⟶ V') (b : V' ⟶ V'') :
    siteExtensionByZeroRestrict W F (a ≫ b) =
      siteExtensionByZeroRestrict W F a ≫ siteExtensionByZeroRestrict W F b := by
  classical
  apply AddCommGrpCat.hom_ext
  dsimp [siteExtensionByZeroRestrict, siteExtensionByZeroSection]
  apply DirectSum.addHom_ext
  intro i x
  simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
  have h (j : V''.unop ⟶ W) (hj : j = b.unop ≫ (a.unop ≫ i))
      (f : Over.mk j ⟶ Over.mk i) (hf : f.left = b.unop ≫ a.unop) :
      DirectSum.of (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ))) j
        ((F.map f.op).hom x) =
      DirectSum.of (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ)))
        (b.unop ≫ (a.unop ≫ i))
        ((F.map (Opposite.op (Over.homMk b.unop :
          Over.mk (b.unop ≫ (a.unop ≫ i)) ⟶ Over.mk (a.unop ≫ i)))).hom
          ((F.map (Opposite.op (Over.homMk a.unop :
            Over.mk (a.unop ≫ i) ⟶ Over.mk i))).hom x)) := by
    subst j
    have hf' : f =
        (Over.homMk b.unop :
          Over.mk (b.unop ≫ (a.unop ≫ i)) ⟶ Over.mk (a.unop ≫ i)) ≫
        (Over.homMk a.unop : Over.mk (a.unop ≫ i) ⟶ Over.mk i) :=
      Over.OverMorphism.ext hf
    simp [hf', Functor.map_comp]
    rfl
  exact h _ (Category.assoc _ _ _) _ rfl

/-- The presheaf with the stated sections and restrictions. Stacks Project, 03DI and 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
noncomputable def siteExtensionByZeroPresheafObj (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max v w} where
  obj V := siteExtensionByZeroSection W F V
  map a := siteExtensionByZeroRestrict W F a
  map_id V := siteExtensionByZeroRestrict_id W F V
  map_comp a b := siteExtensionByZeroRestrict_comp W F a b

open Classical in
/-- A presheaf morphism acts componentwise on each summand. Stacks Project, 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
noncomputable def siteExtensionByZeroHomApp {F G : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (α : F ⟶ G) (V : Cᵒᵖ) :
    siteExtensionByZeroSection W F V ⟶ siteExtensionByZeroSection W G V :=
  AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun φ : V.unop ⟶ W =>
    (DirectSum.of (fun ψ : V.unop ⟶ W => G.obj (Opposite.op (Over.mk ψ))) φ).comp
      (α.app (Opposite.op (Over.mk φ))).hom)

/-- Naturality: evaluate on each injection and use naturality of `α` at the slice map.
Stacks Project, 03EJ (blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
theorem siteExtensionByZeroHomApp_naturality {F G : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (α : F ⟶ G) {V V' : Cᵒᵖ} (a : V ⟶ V') :
    siteExtensionByZeroRestrict W F a ≫ siteExtensionByZeroHomApp W α V' =
      siteExtensionByZeroHomApp W α V ≫ siteExtensionByZeroRestrict W G a := by
  classical
  apply AddCommGrpCat.hom_ext
  dsimp [siteExtensionByZeroRestrict, siteExtensionByZeroHomApp,
    siteExtensionByZeroSection]
  apply DirectSum.addHom_ext
  intro i x
  simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
  congr 1
  exact ConcreteCategory.congr_hom (α.naturality
    (Opposite.op (Over.homMk a.unop : Over.mk (a.unop ≫ i) ⟶ Over.mk i))) x

/-- The induced natural transformation. Stacks Project, 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
noncomputable def siteExtensionByZeroHom {F G : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (α : F ⟶ G) : siteExtensionByZeroPresheafObj W F ⟶ siteExtensionByZeroPresheafObj W G where
  app V := siteExtensionByZeroHomApp W α V
  naturality _ _ a := siteExtensionByZeroHomApp_naturality W α a

/-- Identity morphisms act identically on each summand; extensionality on sections and
injections proves the claim. Stacks Project, 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
theorem siteExtensionByZeroHom_id (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    siteExtensionByZeroHom W (𝟙 F) = 𝟙 (siteExtensionByZeroPresheafObj W F) := by
  classical
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  dsimp [siteExtensionByZeroHom, siteExtensionByZeroHomApp,
    siteExtensionByZeroSection, siteExtensionByZeroPresheafObj]
  apply DirectSum.addHom_ext
  intro i x
  simp

/-- Composition acts by the composite component on each summand; use extensionality on
sections and injections. Stacks Project, 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
theorem siteExtensionByZeroHom_comp {F G H : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (α : F ⟶ G) (β : G ⟶ H) :
    siteExtensionByZeroHom W (α ≫ β) =
      siteExtensionByZeroHom W α ≫ siteExtensionByZeroHom W β := by
  classical
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  dsimp [siteExtensionByZeroHom, siteExtensionByZeroHomApp,
    siteExtensionByZeroSection, siteExtensionByZeroPresheafObj]
  apply DirectSum.addHom_ext
  intro i x
  simp

/-- Presheaf extension by zero from the slice: direct sums over arrows to `W`, restriction
by precomposition, and componentwise action on morphisms. Stacks Project, 03DI and 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
noncomputable def siteExtensionByZeroPresheaf :
    ((Over W)ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) where
  obj F := siteExtensionByZeroPresheafObj W F
  map α := siteExtensionByZeroHom W α
  map_id F := siteExtensionByZeroHom_id W F
  map_comp α β := siteExtensionByZeroHom_comp W α β

/-- Forgetting scalars in the module construction gives the same direct sums and
restrictions. In particular this applies to the constant integer ring sheaf, where modules
are abelian groups. Proof: compare the section types and maps; their formulas agree on every
injection, and functor extensionality concludes. Stacks Project, 03DI and 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
theorem siteExtensionByZeroPresheaf_modules {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (G : SheafOfModules.{w} (R.over W)) :
    (siteExtensionByZeroPresheaf W).obj G.val.presheaf =
      (PresheafOfModules.toPresheaf R.obj).obj
        ((SheafOfModules.extensionByZeroPresheaf R W).obj G) := by
  rfl


end

/-- Sheaf extension by zero `j_{W!}`: on the site `(C, J)` (the precoverage form of
`def-weil-pbc-sites-and-cohomology`), give `C/W` the localized topology
`J.toGrothendieck.over W` (a sieve over `W` covers when its underlying sieve covers in `C`),
apply the presheaf construction to the underlying presheaf of a sheaf, and sheafify for
`J.toGrothendieck`. Stacks Project, 03DI and 03EJ
(blueprint: def-weil-pbc-site-extension-by-zero-presheaf). -/
noncomputable def siteExtensionByZeroSheaf {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks] (W : C) :
    Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{u} ⥤
      Sheaf J.toGrothendieck AddCommGrpCat.{u} :=
  sheafToPresheaf (J.toGrothendieck.over W) AddCommGrpCat.{u} ⋙
    siteExtensionByZeroPresheaf W ⋙ presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}

end CategoryTheory

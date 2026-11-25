/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Derived Hom on finite disjoint unions of pro-etale objects

## References

* Stacks Project, Tags 04TS (gluing sheaves), 015F (exact derived functors), and 0F63 (finite
  disjoint union criterion)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false

namespace CategoryTheory

private theorem conjugateComparison
    {E F : Type*} [Category E] [Category F] (T : E ⥤ F)
    {x₁ x₂ q₁ q₂ : E} {y₁ y₂ r₁ r₂ : F}
    (a₁ : x₁ ≅ q₁) (a₂ : x₂ ≅ q₂) (b₁ : y₁ ≅ r₁) (b₂ : y₂ ≅ r₂)
    (e₁ : T.obj x₁ ≅ y₁) (e₂ : T.obj x₂ ≅ y₂)
    (d₁ : T.obj q₁ ≅ r₁) (d₂ : T.obj q₂ ≅ r₂)
    (f : q₁ ⟶ q₂) (t : r₁ ⟶ r₂)
    (h₁ : e₁.hom ≫ b₁.hom = T.map a₁.hom ≫ d₁.hom)
    (h₂ : e₂.hom ≫ b₂.hom = T.map a₂.hom ≫ d₂.hom)
    (ht : T.map f ≫ d₂.hom = d₁.hom ≫ t) :
    e₁.inv ≫ T.map (a₁.hom ≫ f ≫ a₂.inv) ≫ e₂.hom =
      b₁.hom ≫ t ≫ b₂.inv := by
  rw [← cancel_epi e₁.hom, ← cancel_mono b₂.hom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  rw [h₂]
  simp only [← T.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  rw [Functor.map_comp, Category.assoc, ht, ← Category.assoc, ← h₁]
  simp only [Category.assoc, Category.comp_id]

section ModuleExtension

variable {C : Type (u + 1)} [Category.{u} C]
  (B : Type (u + 1)) [CommRing B] (W : C)

open Classical in
private noncomputable def moduleExtensionByZeroSection (F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B)
    (V : Cᵒᵖ) : ModuleCat.{u + 1} B :=
  ModuleCat.of B (DirectSum (V.unop ⟶ W)
    (fun φ => F.obj (Opposite.op (Over.mk φ))))

open Classical in
private noncomputable def moduleExtensionByZeroRestrict (F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B)
    {V V' : Cᵒᵖ} (a : V ⟶ V') :
    moduleExtensionByZeroSection B W F V ⟶ moduleExtensionByZeroSection B W F V' :=
  ModuleCat.ofHom (DirectSum.toModule B _ _ fun φ : V.unop ⟶ W =>
    (DirectSum.lof B _ (fun ψ : V'.unop ⟶ W => F.obj (Opposite.op (Over.mk ψ)))
      (a.unop ≫ φ)).comp
        (F.map (Opposite.op (Over.homMk a.unop :
          Over.mk (a.unop ≫ φ) ⟶ Over.mk φ))).hom)

private theorem moduleExtensionByZeroRestrict_id (F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B) (V : Cᵒᵖ) :
    moduleExtensionByZeroRestrict B W F (𝟙 V) = 𝟙 (moduleExtensionByZeroSection B W F V) := by
  classical
  apply ModuleCat.hom_ext
  dsimp [moduleExtensionByZeroRestrict, moduleExtensionByZeroSection]
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simp only [DirectSum.toModule_lof, LinearMap.comp_apply, LinearMap.id_apply]
  have h (j : V.unop ⟶ W) (hj : j = i)
      (f : Over.mk j ⟶ Over.mk i) (hf : f.left = 𝟙 V.unop) :
      DirectSum.lof B _ (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ))) j
        ((F.map f.op).hom x) =
      DirectSum.lof B _ (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ))) i x := by
    subst j
    have hf' : f = 𝟙 (Over.mk i) := Over.OverMorphism.ext hf
    simp [hf']
  exact h _ (Category.id_comp i) (Over.homMk (𝟙 V.unop)) rfl

private theorem moduleExtensionByZeroRestrict_comp (F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B)
    {V V' V'' : Cᵒᵖ} (a : V ⟶ V') (b : V' ⟶ V'') :
    moduleExtensionByZeroRestrict B W F (a ≫ b) =
      moduleExtensionByZeroRestrict B W F a ≫ moduleExtensionByZeroRestrict B W F b := by
  classical
  apply ModuleCat.hom_ext
  dsimp [moduleExtensionByZeroRestrict, moduleExtensionByZeroSection]
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
  have h (j : V''.unop ⟶ W) (hj : j = b.unop ≫ (a.unop ≫ i))
      (f : Over.mk j ⟶ Over.mk i) (hf : f.left = b.unop ≫ a.unop) :
      DirectSum.lof B _ (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ))) j
        ((F.map f.op).hom x) =
      DirectSum.lof B _ (fun ψ ↦ F.obj (Opposite.op (Over.mk ψ)))
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
  exact h _ (Category.assoc _ _ _) (Over.homMk (b.unop ≫ a.unop)) rfl

private noncomputable def moduleExtensionByZeroPresheafObj (F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B) :
    Cᵒᵖ ⥤ ModuleCat.{u + 1} B where
  obj V := moduleExtensionByZeroSection B W F V
  map a := moduleExtensionByZeroRestrict B W F a
  map_id V := moduleExtensionByZeroRestrict_id B W F V
  map_comp a b := moduleExtensionByZeroRestrict_comp B W F a b

open Classical in
private noncomputable def moduleExtensionByZeroHomApp {F G : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B}
    (α : F ⟶ G) (V : Cᵒᵖ) :
    moduleExtensionByZeroSection B W F V ⟶ moduleExtensionByZeroSection B W G V :=
  ModuleCat.ofHom (DirectSum.toModule B _ _ fun φ : V.unop ⟶ W =>
    (DirectSum.lof B _ (fun ψ : V.unop ⟶ W => G.obj (Opposite.op (Over.mk ψ))) φ).comp
      (α.app (Opposite.op (Over.mk φ))).hom)

private theorem moduleExtensionByZeroHomApp_naturality {F G : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B}
    (α : F ⟶ G) {V V' : Cᵒᵖ} (a : V ⟶ V') :
    moduleExtensionByZeroRestrict B W F a ≫ moduleExtensionByZeroHomApp B W α V' =
      moduleExtensionByZeroHomApp B W α V ≫ moduleExtensionByZeroRestrict B W G a := by
  classical
  apply ModuleCat.hom_ext
  dsimp [moduleExtensionByZeroRestrict, moduleExtensionByZeroHomApp,
    moduleExtensionByZeroSection]
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
  exact congrArg (DirectSum.lof B _ (fun ψ ↦ G.obj (op (Over.mk ψ))) (a.unop ≫ i))
    (ConcreteCategory.congr_hom (α.naturality
      (Opposite.op (Over.homMk a.unop : Over.mk (a.unop ≫ i) ⟶ Over.mk i))) x)

private noncomputable def moduleExtensionByZeroHom {F G : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B}
    (α : F ⟶ G) : moduleExtensionByZeroPresheafObj B W F ⟶
      moduleExtensionByZeroPresheafObj B W G where
  app V := moduleExtensionByZeroHomApp B W α V
  naturality _ _ a := moduleExtensionByZeroHomApp_naturality B W α a

private theorem moduleExtensionByZeroHom_id (F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B) :
    moduleExtensionByZeroHom B W (𝟙 F) = 𝟙 (moduleExtensionByZeroPresheafObj B W F) := by
  classical
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  dsimp [moduleExtensionByZeroHom, moduleExtensionByZeroHomApp,
    moduleExtensionByZeroSection, moduleExtensionByZeroPresheafObj]
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simp

private theorem moduleExtensionByZeroHom_comp {F G H : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B}
    (α : F ⟶ G) (β : G ⟶ H) :
    moduleExtensionByZeroHom B W (α ≫ β) =
      moduleExtensionByZeroHom B W α ≫ moduleExtensionByZeroHom B W β := by
  classical
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  dsimp [moduleExtensionByZeroHom, moduleExtensionByZeroHomApp,
    moduleExtensionByZeroSection, moduleExtensionByZeroPresheafObj]
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simp

private noncomputable def moduleExtensionByZeroPresheaf :
    ((Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B) ⥤ (Cᵒᵖ ⥤ ModuleCat.{u + 1} B) where
  obj F := moduleExtensionByZeroPresheafObj B W F
  map α := moduleExtensionByZeroHom B W α
  map_id F := moduleExtensionByZeroHom_id B W F
  map_comp α β := moduleExtensionByZeroHom_comp B W α β

private abbrev sliceRestrict (W : C) :=
  (Functor.whiskeringLeft (Over W)ᵒᵖ Cᵒᵖ (ModuleCat.{u + 1} B)).obj (Over.forget W).op

private noncomputable def sumLift (W : C)
    {F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B}
    {G : Cᵒᵖ ⥤ ModuleCat.{u + 1} B} (α : F ⟶ (sliceRestrict B W).obj G) :
    (moduleExtensionByZeroPresheaf B W).obj F ⟶ G := by
  classical
  exact {
    app V := ModuleCat.ofHom (DirectSum.toModule B _ _ fun φ ↦
      (α.app (Opposite.op (Over.mk φ))).hom)
    naturality V V' a := by
      classical
      apply ModuleCat.hom_ext
      dsimp [moduleExtensionByZeroPresheaf, moduleExtensionByZeroPresheafObj,
        moduleExtensionByZeroRestrict, moduleExtensionByZeroSection]
      apply DirectSum.linearMap_ext
      intro φ
      ext x : 1
      simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
      exact ConcreteCategory.congr_hom (α.naturality
        (Opposite.op (Over.homMk a.unop : Over.mk (a.unop ≫ φ) ⟶ Over.mk φ))) x }

private noncomputable def sumRestrict (W : C)
    {F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B}
    {G : Cᵒᵖ ⥤ ModuleCat.{u + 1} B}
    (β : (moduleExtensionByZeroPresheaf B W).obj F ⟶ G) :
    F ⟶ (sliceRestrict B W).obj G := by
  classical
  exact {
    app Y := ModuleCat.ofHom
      (DirectSum.lof B _ (fun φ : Y.unop.left ⟶ W ↦ F.obj (Opposite.op (Over.mk φ)))
        Y.unop.hom) ≫ β.app (Opposite.op Y.unop.left)
    naturality Y Y' a := by
      classical
      apply ModuleCat.hom_ext
      ext x : 1
      have h := ConcreteCategory.congr_hom (β.naturality ((Over.forget W).op.map a))
        (DirectSum.lof B _ (fun φ : Y.unop.left ⟶ W ↦ F.obj (Opposite.op (Over.mk φ)))
          Y.unop.hom x)
      dsimp [moduleExtensionByZeroPresheaf, moduleExtensionByZeroPresheafObj,
        moduleExtensionByZeroRestrict, moduleExtensionByZeroSection] at h
      simp only [LinearMap.comp_apply, DirectSum.toModule_lof] at h
      have aux (j : Y'.unop.left ⟶ W) (hj : j = Y'.unop.hom)
          (f : Over.mk j ⟶ Y.unop) (hf : f.left = a.unop.left) :
          DirectSum.lof B _ (fun φ ↦ F.obj (Opposite.op (Over.mk φ))) j
            ((F.map f.op).hom x) =
          DirectSum.lof B _ (fun φ ↦ F.obj (Opposite.op (Over.mk φ))) Y'.unop.hom
            ((F.map a).hom x) := by
        subst j
        have he : f = a.unop := Over.OverMorphism.ext hf
        subst f
        rfl
      have aux' := aux (a.unop.left ≫ Y.unop.hom) (Over.w a.unop)
        (Over.homMk a.unop.left : Over.mk (a.unop.left ≫ Y.unop.hom) ⟶ Y.unop) rfl
      erw [aux'] at h
      exact h }

private noncomputable def sumHomEquiv (W : C)
    (F : (Over W)ᵒᵖ ⥤ ModuleCat.{u + 1} B)
    (G : Cᵒᵖ ⥤ ModuleCat.{u + 1} B) :
    ((moduleExtensionByZeroPresheaf B W).obj F ⟶ G) ≃
      (F ⟶ (sliceRestrict B W).obj G) where
  toFun := sumRestrict B W
  invFun := sumLift B W
  left_inv β := by
    classical
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro φ
    ext x : 1
    simp [sumLift, sumRestrict]
  right_inv α := by
    classical
    apply NatTrans.ext
    funext Y
    apply ModuleCat.hom_ext
    ext x : 1
    dsimp [sumLift, sumRestrict]
    erw [DirectSum.toModule_lof]
    rfl

private noncomputable def sumAdjunction (W : C) :
    moduleExtensionByZeroPresheaf B W ⊣ sliceRestrict B W :=
  Adjunction.mkOfHomEquiv {
    homEquiv := sumHomEquiv B W
    homEquiv_naturality_left_symm := by
      intro F' F G α β
      classical
      apply NatTrans.ext
      funext V
      apply ModuleCat.hom_ext
      apply DirectSum.linearMap_ext
      intro φ
      ext x : 1
      dsimp [sumHomEquiv, sumLift, moduleExtensionByZeroPresheaf, moduleExtensionByZeroHom,
        moduleExtensionByZeroHomApp]
      erw [DirectSum.toModule_lof, LinearMap.comp_apply, DirectSum.toModule_lof]
      erw [LinearMap.comp_apply, DirectSum.toModule_lof]
    homEquiv_naturality_right := by
      intro F G G' α β
      apply NatTrans.ext
      funext Y
      simp [sumHomEquiv, sumRestrict, sliceRestrict, Category.assoc] }

private theorem moduleRestrictionPreservesKInjectives
    (J : GrothendieckTopology C) [EssentiallySmall.{u + 1} C] :
    (J.overPullback (ModuleCat.{u + 1} B) W).PreservesKInjectiveComplexes := by
  let P := moduleExtensionByZeroPresheaf B W
  let L := sheafToPresheaf (J.over W) (ModuleCat.{u + 1} B) ⋙ P ⋙
    presheafToSheaf J (ModuleCat.{u + 1} B)
  have hP : P.PreservesMonomorphisms := by
    constructor
    intro X Y α hα
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro V
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (moduleExtensionByZeroHomApp B W α V).hom
    have hmap : (moduleExtensionByZeroHomApp B W α V).hom =
        DirectSum.lmap (R := B) (fun φ : V.unop ⟶ W ↦
          (α.app (op (Over.mk φ))).hom) := by
      classical
      apply DirectSum.linearMap_ext
      intro φ
      ext x : 1
      simp [moduleExtensionByZeroHomApp, moduleExtensionByZeroSection]
    rw [hmap]
    apply (DirectSum.lmap_injective _).mpr
    intro φ
    exact (ModuleCat.mono_iff_injective _).mp (inferInstance)
  let adj : L ⊣ J.overPullback (ModuleCat.{u + 1} B) W :=
    ((sumAdjunction B W).comp (sheafificationAdjunction J (ModuleCat.{u + 1} B)))
      |>.restrictFullyFaithful
        (fullyFaithfulSheafToPresheaf (J.over W) (ModuleCat.{u + 1} B))
        (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  have : L.PreservesMonomorphisms := inferInstance
  have : L.Additive := adj.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L := inferInstance
  have : L.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels L
  have : PreservesFiniteLimits L := L.preservesFiniteLimits_of_preservesHomology
  exact adj.preservesKInjectiveComplexes

end ModuleExtension

section InjectiveRepresentatives

variable {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
  (K L : CochainComplex E ℤ) [L.IsKInjective]

private theorem injectiveQMap_surjective :
    Function.Surjective (DerivedCategory.Q.map : (K ⟶ L) → _) := by
  intro f
  let e := DerivedCategory.quotientCompQhIso E
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ (.up ℤ)).obj K) L).2
      (e.hom.app K ≫ f ≫ e.inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi (e.hom.app K)]
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  dsimp only [e]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem injectiveQMap_eq_iff (f g : K ⟶ L) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g ↔ Nonempty (Homotopy f g) := by
  constructor
  · intro h
    refine ⟨HomotopyCategory.homotopyOfEq f g ?_⟩
    apply (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K) L).1
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso E).hom.app L)]
    simp only [DerivedCategory.quotientCompQhIso_hom_naturality, h]
  · rintro ⟨h⟩
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso E).hom.app K)]
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality,
      ← DerivedCategory.quotientCompQhIso_hom_naturality,
      HomotopyCategory.eq_of_homotopy f g h]

end InjectiveRepresentatives

section FiniteProducts

variable {C : Type (u + 1)} [Category.{u} C]
  [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
  (B : Type (u + 1)) [CommRing B]
  (I : Type (u + 1)) (W : I → C) (c : Cofan W)
  (hsec : ∀ H : Sheaf J (Type (u + 1)),
    Function.Bijective (fun t : H.obj.obj (op c.pt) ↦
      fun i ↦ H.obj.map (c.inj i).op t))

include hsec

omit [EssentiallySmall.{u + 1} C] in
private theorem moduleHomProducts (M N : Sheaf J (ModuleCat.{u + 1} B)) :
    Function.Bijective (fun f : M.over c.pt ⟶ N.over c.pt ↦
      fun i ↦ (J.overMapPullback (ModuleCat.{u + 1} B) (c.inj i)).map f) := by
  exact hsec (sheafHom M N)

private abbrev complexRestriction (U : C) :=
  (J.overPullback (ModuleCat.{u + 1} B) U).mapHomologicalComplex (.up ℤ)

private abbrev complexRelocalization {U V : C} (f : V ⟶ U) :=
  (J.overMapPullback (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)

omit [EssentiallySmall.{u + 1} C] in
private theorem complexHomProducts
    (K L : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ) :
    Function.Bijective (fun f : (complexRestriction J B c.pt).obj K ⟶
        (complexRestriction J B c.pt).obj L ↦
      fun i ↦ (complexRelocalization J B (c.inj i)).map f) := by
  constructor
  · intro f g h
    ext n : 1
    apply (moduleHomProducts J B I W c hsec (K.X n) (L.X n)).1
    funext i
    exact congrArg (fun z ↦ z.f n) (congrFun h i)
  · intro f
    choose a ha using fun n ↦
      (moduleHomProducts J B I W c hsec (K.X n) (L.X n)).2 (fun i ↦ (f i).f n)
    dsimp only at ha
    have comm (p q : ℤ) :
        ((complexRestriction J B c.pt).obj K).d p q ≫ a q =
          a p ≫ ((complexRestriction J B c.pt).obj L).d p q := by
      apply (moduleHomProducts J B I W c hsec (K.X p) (L.X q)).1
      funext i
      simp only [Functor.map_comp]
      erw [congrFun (ha p) i, congrFun (ha q) i]
      exact ((f i).comm p q).symm
    refine ⟨{ f := a, comm' := fun p q _ ↦ (comm p q).symm }, ?_⟩
    funext i
    ext n : 1
    exact congrFun (ha n) i

omit [EssentiallySmall.{u + 1} C] in
private theorem complexHomotopyProducts
    (K L : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ)
    (f g : (complexRestriction J B c.pt).obj K ⟶
      (complexRestriction J B c.pt).obj L)
    (h : ∀ i, Nonempty (Homotopy
      ((complexRelocalization J B (c.inj i)).map f)
      ((complexRelocalization J B (c.inj i)).map g))) : Nonempty (Homotopy f g) := by
  classical
  let h := fun i ↦ (h i).some
  choose a ha using fun p q ↦
    (moduleHomProducts J B I W c hsec (K.X p) (L.X q)).2 (fun i ↦ (h i).hom p q)
  dsimp only at ha
  refine ⟨{ hom := a, zero := ?_, comm := ?_ }⟩
  · intro p q hpq
    apply (moduleHomProducts J B I W c hsec (K.X p) (L.X q)).1
    funext i
    dsimp only
    erw [congrFun (ha p q) i, (h i).zero p q hpq]
    rfl
  · intro n
    apply (moduleHomProducts J B I W c hsec (K.X n) (L.X n)).1
    funext i
    simp only [dNext, prevD, AddMonoidHom.mk'_apply,
      Functor.map_add, Functor.map_comp]
    erw [congrFun (ha _ _) i, congrFun (ha _ _) i]
    exact (h i).comm n

omit hsec in
private theorem sliceQCoherence {U V : C} (f : V ⟶ U)
    (K : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ) :
    (derivedSliceMapIso J B f).hom.app (DerivedCategory.Q.obj K) ≫
      (J.overPullback (ModuleCat.{u + 1} B) V).mapDerivedCategoryFactors.hom.app K =
    (derivedSliceMap J B f).map
        ((J.overPullback (ModuleCat.{u + 1} B) U).mapDerivedCategoryFactors.hom.app K) ≫
      (J.overMapPullback (ModuleCat.{u + 1} B) f).mapDerivedCategoryFactors.hom.app
        ((complexRestriction J B U).obj K) := by
  let F := J.overPullback (ModuleCat.{u + 1} B) U
  let G := J.overMapPullback (ModuleCat.{u + 1} B) f
  have hc := Functor.mapDerivedCategoryCompIso_fac F G K
  have he := Functor.mapDerivedCategoryNatIso_fac (sliceRestrictionMapIso J B f) K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).hom.app K = 𝟙 _ := by
    ext n
    rfl
  have hid' : (NatTrans.mapHomologicalComplex
      (sliceRestrictionMapIso J B f).hom (.up ℤ)).app K = 𝟙 _ := by
    ext n : 1
    rfl
  rw [hid] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  rw [hid'] at he
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at he
  simp only [derivedSliceMapIso, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [he]
  change (F.mapDerivedCategoryCompIso G).hom.app _ ≫ _ = _
  erw [← hc, Iso.hom_inv_id_app_assoc]

omit hsec in
private noncomputable def localQMap
    (K L : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ) (U : C)
    (f : (complexRestriction J B U).obj K ⟶ (complexRestriction J B U).obj L) :
    (derivedSliceRestriction J B U).obj (DerivedCategory.Q.obj K) ⟶
      (derivedSliceRestriction J B U).obj (DerivedCategory.Q.obj L) :=
  (J.overPullback (ModuleCat.{u + 1} B) U).mapDerivedCategoryFactors.hom.app K ≫
    DerivedCategory.Q.map f ≫
      (J.overPullback (ModuleCat.{u + 1} B) U).mapDerivedCategoryFactors.inv.app L

omit hsec in
private theorem localQMap_restrict
    (K L : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ)
    {U V : C} (g : V ⟶ U)
    (f : (complexRestriction J B U).obj K ⟶ (complexRestriction J B U).obj L) :
    derivedLocalHomRestriction J B (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) g
        (localQMap J B K L U f) =
      localQMap J B K L V ((complexRelocalization J B g).map f) := by
  let G := J.overMapPullback (ModuleCat.{u + 1} B) g
  let e := derivedSliceMapIso J B g
  let a := (J.overPullback (ModuleCat.{u + 1} B) U).mapDerivedCategoryFactors
  let b := (J.overPullback (ModuleCat.{u + 1} B) V).mapDerivedCategoryFactors
  let d := G.mapDerivedCategoryFactors
  have hK := sliceQCoherence J B g K
  have hL := sliceQCoherence J B g L
  change e.hom.app _ ≫ b.hom.app K =
    G.mapDerivedCategory.map (a.hom.app K) ≫ d.hom.app _ at hK
  change e.hom.app _ ≫ b.hom.app L =
    G.mapDerivedCategory.map (a.hom.app L) ≫ d.hom.app _ at hL
  exact conjugateComparison G.mapDerivedCategory (a.app K) (a.app L)
    (b.app K) (b.app L) (e.app (DerivedCategory.Q.obj K))
    (e.app (DerivedCategory.Q.obj L))
    (d.app ((complexRestriction J B U).obj K))
    (d.app ((complexRestriction J B U).obj L))
    (DerivedCategory.Q.map f) (DerivedCategory.Q.map ((complexRelocalization J B g).map f))
    hK hL (G.mapDerivedCategoryFactors_hom_naturality f)

omit hsec in
private theorem localQMap_surjective
    (K L : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ)
    [L.IsKInjective] (U : C) :
    Function.Surjective (localQMap J B K L U) := by
  have := moduleRestrictionPreservesKInjectives B U J
  intro f
  let a := (J.overPullback (ModuleCat.{u + 1} B) U).mapDerivedCategoryFactors
  obtain ⟨g, hg⟩ := injectiveQMap_surjective
    ((complexRestriction J B U).obj K) ((complexRestriction J B U).obj L)
    (a.inv.app K ≫ f ≫ a.hom.app L)
  refine ⟨g, ?_⟩
  change a.hom.app K ≫ DerivedCategory.Q.map g ≫ a.inv.app L = f
  rw [hg]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact Category.comp_id f

omit hsec in
private theorem localQMap_eq_iff
    (K L : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ)
    [L.IsKInjective] (U : C)
    (f g : (complexRestriction J B U).obj K ⟶ (complexRestriction J B U).obj L) :
    localQMap J B K L U f = localQMap J B K L U g ↔ Nonempty (Homotopy f g) := by
  have := moduleRestrictionPreservesKInjectives B U J
  dsimp only [localQMap]
  rw [cancel_epi, cancel_mono]
  exact injectiveQMap_eq_iff _ _ f g

private theorem derivedHomProductsQ
    (K L : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ) [L.IsKInjective] :
    Function.Bijective (fun f :
      (derivedSliceRestriction J B c.pt).obj (DerivedCategory.Q.obj K) ⟶
        (derivedSliceRestriction J B c.pt).obj (DerivedCategory.Q.obj L) ↦
      fun i ↦ derivedLocalHomRestriction J B
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (c.inj i) f) := by
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := localQMap_surjective J B K L c.pt f
    obtain ⟨g, rfl⟩ := localQMap_surjective J B K L c.pt g
    apply (localQMap_eq_iff J B K L c.pt f g).2
    apply complexHomotopyProducts J B I W c hsec K L f g
    intro i
    apply (localQMap_eq_iff J B K L (W i) _ _).1
    simpa only [localQMap_restrict] using congrFun h i
  · intro f
    choose g hg using fun i ↦ localQMap_surjective J B K L (W i) (f i)
    obtain ⟨a, ha⟩ := (complexHomProducts J B I W c hsec K L).2 g
    refine ⟨localQMap J B K L c.pt a, ?_⟩
    funext i
    dsimp only
    rw [localQMap_restrict]
    dsimp only at ha
    rw [congrFun ha i, hg i]

private theorem derivedHomProducts
    (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    Function.Bijective (fun f :
      (derivedSliceRestriction J B c.pt).obj A ⟶
        (derivedSliceRestriction J B c.pt).obj D ↦
      fun i ↦ derivedLocalHomRestriction J B A D (c.inj i) f) := by
  obtain ⟨K, _, ⟨eA⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective A
  obtain ⟨L, _, ⟨eD⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective D
  let e (U : C) := Iso.homCongr
    ((derivedSliceRestriction J B U).mapIso eA)
    ((derivedSliceRestriction J B U).mapIso eD)
  have hres (i : I)
      (f : (derivedSliceRestriction J B c.pt).obj A ⟶
        (derivedSliceRestriction J B c.pt).obj D) :
      e (W i) (derivedLocalHomRestriction J B A D (c.inj i) f) =
        derivedLocalHomRestriction J B (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (c.inj i) (e c.pt f) := by
    exact derivedLocalHomPresheafMap_natural eA.inv eD.hom c.pt (W i) (c.inj i) f
  have hQ := derivedHomProductsQ J B I W c hsec K L
  constructor
  · intro f g h
    apply (e c.pt).injective
    apply hQ.1
    funext i
    dsimp only
    rw [← hres, ← hres]
    exact congrArg (e (W i)) (congrFun h i)
  · intro f
    obtain ⟨a, ha⟩ := hQ.2 (fun i ↦ e (W i) (f i))
    refine ⟨(e c.pt).symm a, ?_⟩
    funext i
    apply (e (W i)).injective
    rw [hres, Equiv.apply_symm_apply]
    exact congrFun ha i

end FiniteProducts

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Local derived Hom carries a finite disjoint union, detected by its set sheaves,
to a product, including the empty union. -/
theorem proEtaleDerivedHom_finiteProducts (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B]
    (I : Type (u + 1)) [Finite I] (W : I → X.ProEt) (c : Cofan W)
    (_hc : IsColimit c)
    (hsec : ∀ H : Sheaf (ProEt.topology X) (Type (u + 1)),
      Function.Bijective (fun t : H.obj.obj (op c.pt) ↦
        fun i ↦ H.obj.map (c.inj i).op t))
    (A D : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))) :
    Function.Bijective (fun f : (derivedSliceRestriction (ProEt.topology X) B c.pt).obj A ⟶
      (derivedSliceRestriction (ProEt.topology X) B c.pt).obj D ↦
      fun i ↦ derivedLocalHomRestriction (ProEt.topology X) B A D (c.inj i) f) := by
  exact derivedHomProducts (ProEt.topology X) B I W c hsec A D

end AlgebraicGeometry.Scheme

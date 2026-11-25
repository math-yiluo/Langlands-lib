/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.ExchangeFormalism.Basic

/-!
# Coherence of the composition isomorphisms in an exchange formalism

In a `CategoryTheory.ExchangeFormalism`, the composition isomorphisms of the
pushforwards `f_*` and of the extensions by zero `j_!` are conjugate to those of the pullbacks.
This file transports the associativity of the pullback pseudofunctor to them.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism



variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Pullback

variable {X Y Z W : 𝒞}

/-- The associativity of the composition isomorphisms of the pullbacks, for their inverses. -/
lemma pbComp'_assoc_inv (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W)
    (fgh : X ⟶ W) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) :
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (F.pb h) (F.pbComp' f g fg hfg).inv ≫
        (F.pbComp' fg h fgh hfgh).inv =
      Functor.whiskerRight (F.pbComp' g h gh hgh).inv (F.pb f) ≫
        (F.pbComp' f gh fgh (by rw [← hfgh, ← hfg, ← hgh, Category.assoc])).inv := by
  have h' : f ≫ gh = fgh := by rw [← hfgh, ← hfg, ← hgh, Category.assoc]
  ext M
  have := F.pbComp'_assoc f g h fg gh fgh hfg hgh hfgh M
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp]
  rw [← cancel_epi ((F.pb f).map ((F.pbComp' g h gh hgh).hom.app M)),
    ← cancel_epi ((F.pbComp' f gh fgh h').hom.app M), ← reassoc_of% this]
  simp [← Functor.map_comp_assoc]

end Pullback

section Pushforward

variable {X Y Z W : 𝒞}

lemma pfComp'_hom (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    (F.pfComp' f g h w).hom =
      conjugateEquiv (F.adj h) ((F.adj g).comp (F.adj f)) (F.pbComp' f g h w).inv :=
  rfl

lemma pfComp'_inv (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    (F.pfComp' f g h w).inv =
      conjugateEquiv ((F.adj g).comp (F.adj f)) (F.adj h) (F.pbComp' f g h w).hom :=
  rfl

/-- **Associativity of the composition isomorphisms of the pushforwards.** -/
lemma pfComp'_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W)
    (fgh : X ⟶ W) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) :
    (F.pfComp' fg h fgh hfgh).hom ≫ Functor.whiskerRight (F.pfComp' f g fg hfg).hom (F.pf h) ≫
        (Functor.associator _ _ _).hom =
      (F.pfComp' f gh fgh (by rw [← hfgh, ← hfg, ← hgh, Category.assoc])).hom ≫
        Functor.whiskerLeft (F.pf f) (F.pfComp' g h gh hgh).hom := by
  rw [pfComp'_hom, pfComp'_hom, pfComp'_hom, pfComp'_hom,
    ← conjugateEquiv_whiskerLeft _ _ (F.adj h),
    ← conjugateEquiv_associator_hom (F.adj h) (F.adj g) (F.adj f),
    ← conjugateEquiv_whiskerRight _ _ (F.adj f), conjugateEquiv_comp, conjugateEquiv_comp,
    conjugateEquiv_comp, Category.assoc, F.pbComp'_assoc_inv f g h fg gh fgh hfg hgh hfgh]


/-- The associativity of the composition isomorphisms of the pushforwards, objectwise, for
their inverses. -/
@[reassoc]
lemma pfComp'_assoc_inv_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W)
    (fgh : X ⟶ W) (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh)
    (h' : f ≫ gh = fgh) (M : F.obj X) :
    (F.pfComp' g h gh hgh).inv.app ((F.pf f).obj M) ≫ (F.pfComp' f gh fgh h').inv.app M =
      (F.pf h).map ((F.pfComp' f g fg hfg).inv.app M) ≫ (F.pfComp' fg h fgh hfgh).inv.app M := by
  have := congr_app (F.pfComp'_assoc f g h fg gh fgh hfg hgh hfgh) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id, Functor.comp_obj] at this
  rw [← cancel_epi ((F.pfComp' g h gh hgh).hom.app ((F.pf f).obj M)),
    ← cancel_epi ((F.pfComp' f gh fgh h').hom.app M)]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  rw [← reassoc_of% this]
  simp [← Functor.map_comp_assoc]

end Pushforward


section ExtensionByZero

variable {A B C D : 𝒞}

/-- The composition isomorphism of the extensions by zero is conjugate to the inverse of the
composition isomorphism of the pullbacks. -/
lemma conjugateEquiv_shComp'_hom (j₁ : A ⟶ B) (j₂ : B ⟶ C) (j : A ⟶ C) [Fact (𝒪 j₁)]
    [Fact (𝒪 j₂)] [Fact (𝒪 j)] (w : j₁ ≫ j₂ = j) :
    conjugateEquiv ((F.shAdj j₁).comp (F.shAdj j₂)) (F.shAdj j) (F.shComp' j₁ j₂ j w).hom =
      (F.pbComp' j₁ j₂ j w).inv := by
  simp [shComp', conjugateIsoEquiv]

/-- **Associativity of the composition isomorphisms of the extensions by zero.** -/
lemma shComp'_assoc (j₁ : A ⟶ B) (j₂ : B ⟶ C) (j₃ : C ⟶ D) (j₁₂ : A ⟶ C) (j₂₃ : B ⟶ D)
    (j : A ⟶ D) [Fact (𝒪 j₁)] [Fact (𝒪 j₂)] [Fact (𝒪 j₃)]
    [Fact (𝒪 j₁₂)] [Fact (𝒪 j₂₃)] [Fact (𝒪 j)]
    (h₁₂ : j₁ ≫ j₂ = j₁₂) (h₂₃ : j₂ ≫ j₃ = j₂₃) (h : j₁₂ ≫ j₃ = j) (h' : j₁ ≫ j₂₃ = j) :
    (F.shComp' j₁₂ j₃ j h).hom ≫ Functor.whiskerRight (F.shComp' j₁ j₂ j₁₂ h₁₂).hom (F.sh j₃) ≫
        (Functor.associator _ _ _).hom =
      (F.shComp' j₁ j₂₃ j h').hom ≫
        Functor.whiskerLeft (F.sh j₁) (F.shComp' j₂ j₃ j₂₃ h₂₃).hom := by
  apply (conjugateEquiv ((F.shAdj j₁).comp ((F.shAdj j₂).comp (F.shAdj j₃))) (F.shAdj j)).injective
  rw [← conjugateEquiv_comp _ ((F.shAdj j₁).comp (F.shAdj j₂₃)),
    ← conjugateEquiv_comp _ ((F.shAdj j₁₂).comp (F.shAdj j₃)),
    ← conjugateEquiv_comp _ (((F.shAdj j₁).comp (F.shAdj j₂)).comp (F.shAdj j₃)),
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_shComp'_hom, conjugateEquiv_shComp'_hom, conjugateEquiv_shComp'_hom,
    conjugateEquiv_shComp'_hom, Category.assoc, F.pbComp'_assoc_inv j₁ j₂ j₃ j₁₂ j₂₃ j h₁₂ h₂₃ h]

/-- The associativity of the composition isomorphisms of the extensions by zero, objectwise, for
their inverses. -/
@[reassoc]
lemma shComp'_assoc_inv_app (j₁ : A ⟶ B) (j₂ : B ⟶ C) (j₃ : C ⟶ D) (j₁₂ : A ⟶ C)
    (j₂₃ : B ⟶ D) (j : A ⟶ D) [Fact (𝒪 j₁)] [Fact (𝒪 j₂)] [Fact (𝒪 j₃)]
    [Fact (𝒪 j₁₂)] [Fact (𝒪 j₂₃)] [Fact (𝒪 j)]
    (h₁₂ : j₁ ≫ j₂ = j₁₂) (h₂₃ : j₂ ≫ j₃ = j₂₃) (h : j₁₂ ≫ j₃ = j) (h' : j₁ ≫ j₂₃ = j)
    (M : F.obj A) :
    (F.sh j₃).map ((F.shComp' j₁ j₂ j₁₂ h₁₂).inv.app M) ≫ (F.shComp' j₁₂ j₃ j h).inv.app M =
      (F.shComp' j₂ j₃ j₂₃ h₂₃).inv.app ((F.sh j₁).obj M) ≫ (F.shComp' j₁ j₂₃ j h').inv.app M := by
  have := congr_app (F.shComp'_assoc j₁ j₂ j₃ j₁₂ j₂₃ j h₁₂ h₂₃ h h') M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id, Functor.comp_obj] at this
  rw [← cancel_epi ((F.sh j₃).map ((F.shComp' j₁ j₂ j₁₂ h₁₂).hom.app M)),
    ← cancel_epi ((F.shComp' j₁₂ j₃ j h).hom.app M)]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [reassoc_of% this]
  simp

end ExtensionByZero

end CategoryTheory.ExchangeFormalism

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

/-!
# Absolute left derived functors from a resolving class

Source: Stacks Project, Tags 05Q9, 06XN and 05SE
(blueprint: lem-sf-localized-derived-adjunction).

Let `W` be a class of morphisms with a right calculus of fractions and the
two-out-of-three property, `L` a localization functor for `W`, and `P` a class
of objects resolving every object, such that `F` sends `W`-arrows between
`P`-objects to isomorphisms. Then `F` has a pointwise left derived functor, the
counit of any left derived functor of `F` is invertible on `P`, and a left
derived functor of `F` stays a left derived functor after postcomposition with
any functor.

We also show that a saturated multiplicative system consists exactly of the
morphisms inverted by a localization functor, so that it has the two-out-of-three
property.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v uD vD uH vH uJ vJ

namespace CategoryTheory

namespace MorphismProperty

/-- In a saturated multiplicative system, a morphism belongs to the system if and only if
its image under a localization functor is an isomorphism.
Source: Stacks Project, Categories, Tag 05Q9. -/
lemma IsSaturatedMultiplicativeSystem.mem_iff_isIso_map {C : Type u} [Category.{v} C]
    {D : Type uD} [Category.{vD} D] {W : MorphismProperty C}
    (hW : W.IsSaturatedMultiplicativeSystem) (L : C ⥤ D) [L.IsLocalization W]
    {X Y : C} (f : X ⟶ Y) : W f ↔ IsIso (L.map f) := by
  obtain ⟨⟨hl, hr⟩, hsat⟩ := hW
  refine ⟨fun hf ↦ Localization.inverts L W f hf, fun hf ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W (inv (L.map f))
  obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction L W (inv (L.map f))
  have h₁ : L.map (φ.f ≫ f) = L.map φ.s := by
    rw [L.map_comp, ← φ.map_s_comp_map L (Localization.inverts L W), ← hφ]
    simp
  have h₂ : L.map (f ≫ ψ.f) = L.map ψ.s := by
    rw [L.map_comp, ← ψ.map_comp_map_s L (Localization.inverts L W), ← hψ]
    simp
  obtain ⟨Z, t, ht, eq⟩ := (MorphismProperty.map_eq_iff_precomp L W _ _).1 h₁
  obtain ⟨Z', t', ht', eq'⟩ := (MorphismProperty.map_eq_iff_postcomp L W _ _).1 h₂
  refine hsat _ _ _ _ (t ≫ φ.f) f (ψ.f ≫ t') ?_ ?_
  · rw [← Category.assoc, eq']
    exact W.comp_mem _ _ ψ.hs ht'
  · rw [Category.assoc, eq]
    exact W.comp_mem _ _ ht φ.hs

/-- A saturated multiplicative system which admits a localization functor has the
two-out-of-three property. -/
lemma IsSaturatedMultiplicativeSystem.hasTwoOutOfThreeProperty {C : Type u} [Category.{v} C]
    {D : Type uD} [Category.{vD} D] {W : MorphismProperty C}
    (hW : W.IsSaturatedMultiplicativeSystem) (L : C ⥤ D) [L.IsLocalization W] :
    W.HasTwoOutOfThreeProperty := by
  have : W = (isomorphisms D).inverseImage L := by
    ext X Y f
    exact hW.mem_iff_isIso_map L f
  rw [this]
  infer_instance

end MorphismProperty

namespace Functor

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {H : Type uH} [Category.{vH} H]

/-- A functor sending `W`-arrows between objects of a resolving class `P` to isomorphisms has
a pointwise left derived functor.
Source: Stacks Project, Tags 06XN and 05SE. -/
lemma hasPointwiseLeftDerivedFunctor_of_resolving
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] [W.HasTwoOutOfThreeProperty]
    (F : C ⥤ H) (P : Set C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), X' ∈ P ∧ W s)
    (hinv : ∀ (X X' : C) (s : X ⟶ X'), X ∈ P → X' ∈ P → W s → IsIso (F.map s)) :
    F.HasPointwiseLeftDerivedFunctor W := by
  intro X
  obtain ⟨Y, u, hc, hr, _⟩ := resolvingClass_essentialConstancy W F P hres hinv X
  exact (F.hasPointwiseLeftDerivedFunctorAt_iff W.Q W X).2
    (leftDerived_defined_pointwiseKan_bridge W W.Q F X Y hc u hr).1

/-- The counit of a left derived functor of a functor sending `W`-arrows between objects of a
resolving class `P` to isomorphisms is invertible on `P`.
Source: Stacks Project, Tags 06XN and 05SE. -/
lemma isIso_app_of_resolving
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] [W.HasTwoOutOfThreeProperty]
    (L : C ⥤ D) [L.IsLocalization W] (F : C ⥤ H) (P : Set C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), X' ∈ P ∧ W s)
    (hinv : ∀ (X X' : C) (s : X ⟶ X'), X ∈ P → X' ∈ P → W s → IsIso (F.map s))
    (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W] (X : C) (hX : X ∈ P) :
    IsIso (α.app X) := by
  have := hasPointwiseLeftDerivedFunctor_of_resolving W F P hres hinv
  obtain ⟨Y, u, hc, hr, hu⟩ := resolvingClass_essentialConstancy W F P hres hinv X
  obtain ⟨_, π, ⟨hπ⟩, _, hidentity⟩ :=
    leftDerived_defined_pointwiseKan_bridge W L F X Y hc u hr
  let hcanonical :=
    isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor LF α W (L.obj X)
  have hid : W (𝟙 X) := W.id_mem X
  have hπid : IsIso (π.app (StructuredArrow.mk (𝟙 (L.obj X)))) := by
    rw [hidentity hid]
    exact hu hid hX
  have he := hcanonical.conePointUniqueUpToIso_hom_comp hπ
    (StructuredArrow.mk (𝟙 (L.obj X)))
  have he' : (hcanonical.conePointUniqueUpToIso hπ).hom ≫
      π.app (StructuredArrow.mk (𝟙 (L.obj X))) = α.app X := by
    simp only [RightExtension.coneAt_π_app, StructuredArrow.mk_right,
      StructuredArrow.mk_hom_eq_self, Functor.map_id] at he
    exact he.trans (Category.id_comp _)
  rw [← he']
  exact IsIso.comp_isIso' (Iso.isIso_hom _) hπid

/-- For a functor sending `W`-arrows between objects of a resolving class `P` to
isomorphisms, a left derived functor stays a left derived functor after postcomposition
with any functor.
Source: Stacks Project, Tags 06XN and 05SE. -/
lemma isLeftDerivedFunctor_comp_of_resolving
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] [W.HasTwoOutOfThreeProperty]
    (L : C ⥤ D) [L.IsLocalization W] (F : C ⥤ H) (P : Set C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), X' ∈ P ∧ W s)
    (hinv : ∀ (X X' : C) (s : X ⟶ X'), X ∈ P → X' ∈ P → W s → IsIso (F.map s))
    (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W]
    {J : Type uJ} [Category.{vJ} J] (G : H ⥤ J) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G) W := by
  have hinv' (X X' : C) (s : X ⟶ X') (hX : X ∈ P) (hX' : X' ∈ P) (hs : W s) :
      IsIso ((F ⋙ G).map s) := by
    have := hinv X X' s hX hX' hs
    dsimp
    infer_instance
  have := hasPointwiseLeftDerivedFunctor_of_resolving W (F ⋙ G) P hres hinv'
  let φ := ((F ⋙ G).totalLeftDerived L W).leftDerivedLift
    ((F ⋙ G).totalLeftDerivedCounit L W) W (LF ⋙ G)
    ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G)
  have hφ (X : C) (hX : X ∈ P) : IsIso (φ.app (L.obj X)) := by
    have h₁ := isIso_app_of_resolving W L F P hres hinv LF α X hX
    have h₂ := isIso_app_of_resolving W L (F ⋙ G) P hres hinv' _
      ((F ⋙ G).totalLeftDerivedCounit L W) X hX
    have h₃ := ((F ⋙ G).totalLeftDerived L W).leftDerived_fac_app
      ((F ⋙ G).totalLeftDerivedCounit L W) W (LF ⋙ G)
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G) X
    have : IsIso (φ.app (L.obj X) ≫ ((F ⋙ G).totalLeftDerivedCounit L W).app X) := by
      rw [h₃]
      dsimp
      rw [Category.id_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (((F ⋙ G).totalLeftDerivedCounit L W).app X)
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y
    have := Localization.essSurj L W
    obtain ⟨X', s, hX', hs⟩ := hres (L.objPreimage Y)
    rw [NatTrans.isIso_app_iff_of_iso φ
      (Localization.isoOfHom L W s hs ≪≫ L.objObjPreimageIso Y).symm]
    exact hφ X' hX'
  exact (isLeftDerivedFunctor_iff_of_iso _ ((F ⋙ G).totalLeftDerivedCounit L W) W
    (asIso φ) (by simp [φ])).2 inferInstance

/-- For a functor sending `W`-arrows between objects of a resolving class `P` to
isomorphisms, a left derived functor stays a pointwise right Kan extension after
postcomposition with any functor.
Source: Stacks Project, Tags 06XN and 05SE. -/
lemma isPointwiseRightKanExtension_comp_of_resolving
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] [W.HasTwoOutOfThreeProperty]
    (L : C ⥤ D) [L.IsLocalization W] (F : C ⥤ H) (P : Set C)
    (hres : ∀ X : C, ∃ (X' : C) (s : X' ⟶ X), X' ∈ P ∧ W s)
    (hinv : ∀ (X X' : C) (s : X ⟶ X'), X ∈ P → X' ∈ P → W s → IsIso (F.map s))
    (LF : D ⥤ H) (α : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α W]
    {J : Type uJ} [Category.{vJ} J] (G : H ⥤ J) :
    Nonempty (RightExtension.mk (LF ⋙ G)
      ((Functor.associator L LF G).inv ≫
        Functor.whiskerRight α G)).IsPointwiseRightKanExtension := by
  have := isLeftDerivedFunctor_comp_of_resolving W L F P hres hinv LF α G
  have := hasPointwiseLeftDerivedFunctor_of_resolving W (F ⋙ G) P hres
    (fun X X' s hX hX' hs ↦ by
      have := hinv X X' s hX hX' hs
      dsimp
      infer_instance)
  exact ⟨isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor _ _ W⟩

end Functor

end CategoryTheory

end

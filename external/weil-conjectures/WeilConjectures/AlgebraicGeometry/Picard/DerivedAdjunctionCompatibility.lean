/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

@[expose] public section

universe wA wB vA vB uA uB
open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem pro_preserves_at
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T) (X : C)
    (hc : ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) Y) :
    Q.HasPointwiseRightKanExtensionAt F (Q.obj X) ∧
      PreservesLimit (StructuredArrow.proj (Q.obj X) Q ⋙ F) H := by
  classical
  obtain ⟨Y, hY⟩ := hc
  obtain ⟨u, j₀, r, hr, hfactor⟩ := hY.2
  obtain ⟨hlim, π, ⟨hπ⟩, hden, _⟩ :=
    leftDerived_defined_pointwiseKan_bridge W Q F X Y hY u ⟨j₀, r, hr, hfactor⟩
  let u' : (Functor.const (W.Over ⊤ X)).obj (H.obj Y) ⟶
      MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ (F ⋙ H) :=
    { app := fun j ↦ H.map (u.app j)
      naturality := by
        intro i j f
        change 𝟙 _ ≫ H.map (u.app j) = H.map (u.app i) ≫ H.map (F.map f.left)
        rw [Category.id_comp, ← H.map_comp]
        exact H.congr_map (by simpa using u.naturality f) }
  have hr' : u'.app j₀ ≫ H.map r = 𝟙 (H.obj Y) := by
    change H.map (u.app j₀) ≫ H.map r = _
    rw [← H.map_comp, hr]
    exact H.map_id Y
  have hfactor' : ∀ j : W.Over ⊤ X, ∃ (k : W.Over ⊤ X) (a : k ⟶ j₀) (b : k ⟶ j),
      (F ⋙ H).map b.left = (F ⋙ H).map a.left ≫ H.map r ≫ u'.app j := by
    intro j
    obtain ⟨k, a, b, hab⟩ := hfactor j
    refine ⟨k, a, b, ?_⟩
    change H.map (F.map b.left) = _
    change F.map b.left = F.map a.left ≫ r ≫ u.app j at hab
    simp only [hab, H.map_comp]
    rfl
  have hY' : IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ (F ⋙ H)) (H.obj Y) :=
    ⟨hY.1, u', j₀, H.map r, hr', hfactor'⟩
  obtain ⟨_, π', ⟨hπ'⟩, hden', _⟩ :=
    leftDerived_defined_pointwiseKan_bridge W Q (F ⋙ H) X (H.obj Y) hY' u'
      ⟨j₀, H.map r, hr', hfactor'⟩
  have heq (j : StructuredArrow (Q.obj X) Q) : H.map (π.app j) = π'.app j := by
    obtain ⟨a, ha⟩ := Localization.exists_rightFraction Q W j.hom
    let s : W.Over ⊤ X := ⟨Over.mk a.s, a.hs⟩
    let i := StructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv
    let f : i ⟶ j := StructuredArrow.homMk a.f ha.symm
    have hn := π.naturality f
    have hn' := π'.naturality f
    change 𝟙 Y ≫ π.app j = π.app i ≫ F.map a.f at hn
    change 𝟙 (H.obj Y) ≫ π'.app j = π'.app i ≫ (F ⋙ H).map a.f at hn'
    rw [Category.id_comp] at hn hn'
    rw [hn, hn', H.map_comp, hden s, hden' s]
    rfl
  have hiso : Cone.mk (H.obj Y) π' ≅ H.mapCone (Cone.mk Y π) :=
    Cone.ext (Iso.refl _) (fun j ↦ by simpa using (heq j).symm)
  exact ⟨hlim, preservesLimit_of_preserves_limit_cone hπ
    (IsLimit.ofIsoLimit hπ' hiso)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
theorem pro_absolute
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {T : Type*} [Category* T]
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (Q : C ⥤ D) [Q.IsLocalization W] (F : C ⥤ E) (H : E ⥤ T)
    (hc : ∀ X, ∃ Y, IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) Y) :
    H.PreservesRightKanExtension F Q := by
  classical
  have h (X : C) := pro_preserves_at W Q F H X (hc X)
  have : Q.EssSurj := Localization.essSurj Q W
  have : Q.HasPointwiseRightKanExtension F := fun Y ↦
    (Functor.hasPointwiseRightKanExtensionAt_iff_of_iso Q F
      (Q.objObjPreimageIso Y)).1 (h (Q.objPreimage Y)).1
  apply Functor.PreservesRightKanExtension.mk' H F Q
  intro E hE
  have : E.left.IsRightKanExtension E.hom := ⟨⟨hE⟩⟩
  let hp := Functor.isPointwiseRightKanExtensionOfIsRightKanExtension E.left E.hom
  refine ⟨Functor.RightExtension.IsPointwiseRightKanExtension.isUniversal ?_⟩
  intro Y
  have : PreservesLimit (StructuredArrow.proj (Q.obj (Q.objPreimage Y)) Q ⋙ F) H :=
    (h (Q.objPreimage Y)).2
  exact Functor.RightExtension.isPointwiseRightKanExtensionAtOfIso'
    ((Functor.RightExtension.postcompose₂ Q F H).obj E)
    ((hp _).postcompose H) (Q.objObjPreimageIso Y)

end

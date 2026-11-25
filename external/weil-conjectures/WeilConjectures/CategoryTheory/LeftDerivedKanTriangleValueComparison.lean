/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

/-! # Comparing a Kan-extension triangle with denominator values

Source: Stacks Project, Derived Categories, Tags 05SA, 05SU, 05SC.
(blueprint: lem-pur-left-derived-kan-triangle-value-comparison).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[expose] public section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

private theorem kan_value_iso
    {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']
    {L : Type u''} [Category.{v''} L]
    (F : D ⥤ D') (S : MorphismProperty D) [S.HasRightCalculusOfFractions]
    (Q : D ⥤ L) [Q.IsLocalization S] (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] [Q.HasPointwiseRightKanExtension F]
    (X : D) (Y : D')
    (hY : IsEssentiallyConstantProDiagram
      (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F) Y)
    (u : (Functor.const (S.Over ⊤ X)).obj Y ⟶
      MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)
    (hu : ∃ s₀ : S.Over ⊤ X, ∃ r : F.obj s₀.left ⟶ Y,
      u.app s₀ ≫ r = 𝟙 Y ∧
        ∀ s : S.Over ⊤ X, ∃ t : S.Over ⊤ X,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s, F.map b.left = F.map a.left ≫ r ≫ u.app s) :
    ∃ e : LF.obj (Q.obj X) ≅ Y, ∀ s : S.Over ⊤ X,
      e.hom ≫ u.app s =
        LF.map (Localization.isoOfHom Q S s.hom s.prop).inv ≫ α.app s.left := by
  obtain ⟨_, π, ⟨hπ⟩, hlegs, _⟩ :=
    leftDerived_defined_pointwiseKan_bridge S Q F X Y hY u hu
  let hcan := isPointwiseRightKanExtensionOfIsRightKanExtension LF α (Q.obj X)
  let e := hcan.conePointUniqueUpToIso hπ
  refine ⟨e, ?_⟩
  intro s
  have h := hcan.conePointUniqueUpToIso_hom_comp hπ
    (StructuredArrow.mk (Localization.isoOfHom Q S s.hom s.prop).inv)
  rw [hlegs] at h
  simpa [RightExtension.coneAt] using h


private theorem kan_value_map
    {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']
    {L : Type u''} [Category.{v''} L]
    (F : D ⥤ D') (S : MorphismProperty D) [S.HasRightCalculusOfFractions]
    (Q : D ⥤ L) [Q.IsLocalization S] (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F)
    {X Y : D} {A B : D'} (f : X ⟶ Y) (lf : A ⟶ B)
    (uX : (Functor.const (S.Over ⊤ X)).obj A ⟶
      MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)
    (uY : (Functor.const (S.Over ⊤ Y)).obj B ⟶
      MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F)
    (hrY : ∃ s₀ : S.Over ⊤ Y, ∃ r : F.obj s₀.left ⟶ B, uY.app s₀ ≫ r = 𝟙 B)
    (eX : LF.obj (Q.obj X) ≅ A) (eY : LF.obj (Q.obj Y) ≅ B)
    (heX : ∀ s : S.Over ⊤ X, eX.hom ≫ uX.app s =
      LF.map (Localization.isoOfHom Q S s.hom s.prop).inv ≫ α.app s.left)
    (heY : ∀ s : S.Over ⊤ Y, eY.hom ≫ uY.app s =
      LF.map (Localization.isoOfHom Q S s.hom s.prop).inv ≫ α.app s.left)
    (hf : ∀ (s : S.Over ⊤ X) (s' : S.Over ⊤ Y) (f' : s.left ⟶ s'.left),
      s.hom ≫ f = f' ≫ s'.hom → uX.app s ≫ F.map f' = lf ≫ uY.app s') :
    LF.map (Q.map f) ≫ eY.hom = eX.hom ≫ lf := by
  obtain ⟨s₀, r, hr⟩ := hrY
  let : IsSplitMono (uY.app s₀) := IsSplitMono.mk' ⟨r, hr⟩
  obtain ⟨φ, hφ⟩ := (MorphismProperty.LeftFraction.mk f s₀.hom s₀.prop).exists_rightFraction
  let s : S.Over ⊤ X := MorphismProperty.Over.mk ⊤ φ.s φ.hs
  have hden : s.hom ≫ f = φ.f ≫ s₀.hom := hφ
  have hq : Q.map f ≫ (Localization.isoOfHom Q S s₀.hom s₀.prop).inv =
      (Localization.isoOfHom Q S s.hom s.prop).inv ≫ Q.map φ.f := by
    apply (cancel_epi (Localization.isoOfHom Q S s.hom s.prop).hom).mp
    erw [← Category.assoc, Localization.isoOfHom_hom, ← Q.map_comp, hden,
      Q.map_comp]
    simp only [Category.assoc, Localization.isoOfHom_hom_inv_id, Category.comp_id]
    erw [Localization.isoOfHom_hom_inv_id_assoc]
  apply (cancel_mono (uY.app s₀)).mp
  simp only [Category.assoc]
  calc
    _ = LF.map (Q.map f ≫ (Localization.isoOfHom Q S s₀.hom s₀.prop).inv) ≫
        α.app s₀.left := by rw [heY, LF.map_comp, Category.assoc]
    _ = LF.map (Localization.isoOfHom Q S s.hom s.prop).inv ≫
        (Q ⋙ LF).map φ.f ≫ α.app s₀.left := by
      simp only [hq, LF.map_comp, Functor.comp_map, Category.assoc]
    _ = eX.hom ≫ uX.app s ≫ F.map φ.f := by
      erw [α.naturality, ← Category.assoc, ← heX]
      rw [Category.assoc]
    _ = eX.hom ≫ lf ≫ uY.app s₀ := by rw [hf s s₀ φ.f hden]

private theorem kan_value_shift_leg
    {D : Type u} [Category.{v} D] [HasShift D ℤ]
    {D' : Type u'} [Category.{v'} D'] [HasShift D' ℤ]
    {L : Type u''} [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ] (S : MorphismProperty D)
    (Q : D ⥤ L) [Q.IsLocalization S] [Q.CommShift ℤ]
    (LF : L ⥤ D') [LF.CommShift ℤ] (α : Q ⋙ LF ⟶ F)
    [NatTrans.CommShift α ℤ] {X : D} {Y : D'} (e : LF.obj (Q.obj X) ≅ Y)
    (u : (Functor.const (S.Over ⊤ X)).obj Y ⟶
      MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)
    (he : ∀ s : S.Over ⊤ X, e.hom ≫ u.app s =
      LF.map (Localization.isoOfHom Q S s.hom s.prop).inv ≫ α.app s.left)
    (n : ℤ) (s : S.Over ⊤ X) (hs : S ((shiftFunctor D n).map s.hom)) :
    ((Q ⋙ LF).commShiftIso n).hom.app X ≫
        (shiftFunctor D' n).map (e.hom ≫ u.app s) ≫
          (F.commShiftIso n).inv.app s.left =
      LF.map (Localization.isoOfHom Q S ((shiftFunctor D n).map s.hom) hs).inv ≫
        α.app ((shiftFunctor D n).obj s.left) := by
  let : IsIso (Q.map ((shiftFunctor D n).map s.hom)) := Localization.inverts Q S _ hs
  have hnat := (Q ⋙ LF).commShiftIso_hom_naturality s.hom n
  rw [he, (shiftFunctor D' n).map_comp]
  let : IsIso ((Q ⋙ LF).map ((shiftFunctor D n).map s.hom)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  apply (cancel_epi ((Q ⋙ LF).map ((shiftFunctor D n).map s.hom))).mp
  simp only [Category.assoc]
  erw [reassoc_of% hnat]
  simp only [Functor.comp_map]
  simp only [← Functor.map_comp, ← Category.assoc]
  erw [Localization.isoOfHom_hom_inv_id, Localization.isoOfHom_hom_inv_id]
  simp only [Functor.map_id, Category.id_comp]
  rw [NatTrans.shift_app_comm α n]
  simp

/-- Compatible denominator values identify a Kan-extension image triangle.
Source: Stacks Project, Derived Categories, Tags 05SA, 05SU, 05SC;
the value-identification step in Proposition Tag 05SE.
(blueprint: lem-pur-left-derived-kan-triangle-value-comparison).

Proof: Each supplied retraction and common-stage factorization makes its denominator
cone a limit. The pointwise Kan bridge extends it to a structured-arrow limit cone at
Q(T.obj_i), with the same legs at inverse denominators. Pointwise existence everywhere
identifies the supplied universal right Kan extension with the pointwise one. Compare
its three limit cones with the supplied cones, obtaining canonical value isomorphisms.
For the first two maps, choose a target denominator at which the cone leg has a
retraction. A right-fraction square supplies a source denominator over the source map.
The fraction identity and naturality of alpha give the corresponding cone-leg equation;
the supplied equation then identifies the maps by cancellation of the split-mono leg.
For the third map, shift the first chosen denominator, which remains in S. Shift
naturality and the shift-compatibility of alpha identify the shifted Kan cone leg with
the inverse-denominator leg. The same fraction identity and naturality argument now
uses the supplied equation for lh. Cancel the shifted split-mono cone leg followed by
the inverse shift comparison of F. The three isomorphisms and commutative squares
form the desired triangle isomorphism. This requires no distinguishedness of T or of
the supplied triangle, and makes no assertion that either triangle is distinguished. -/
theorem leftDerived_kan_triangle_value_comparison
    (D : Type u) [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (D' : Type u') [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ]
    [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (L : Type u'') [Category.{v''} L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty D)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (Q : D ⥤ L) [Q.CommShift ℤ]
    [Q.IsLocalization S]
    (LF : L ⥤ D') [LF.CommShift ℤ]
    (α : Q ⋙ LF ⟶ F)
    (hLF : LF.IsRightKanExtension α)
    [Q.HasPointwiseRightKanExtension F]
    (hα : NatTrans.CommShift α ℤ) (T : Triangle D) (LX LY LZ : D')
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (hZ : F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s, F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
    (huY : ∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s, F.map b.left = F.map a.left ≫ r ≫ uY.app s)
    (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    (huZ : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
      uZ.app s₀ ≫ r = 𝟙 LZ ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s, F.map b.left = F.map a.left ≫ r ≫ uZ.app s)
    (lf : LX ⟶ LY) (lg : LY ⟶ LZ) (lh : LZ ⟶ (shiftFunctor D' (1 : ℤ)).obj LX)
    (hf : ∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
      (f' : s.left ⟶ s'.left), s.hom ≫ T.mor₁ = f' ≫ s'.hom →
        uX.app s ≫ F.map f' = lf ≫ uY.app s')
    (hg : ∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
      (g' : s.left ⟶ s'.left), s.hom ≫ T.mor₂ = g' ≫ s'.hom →
        uY.app s ≫ F.map g' = lg ≫ uZ.app s')
    (hh : ∀ (s : S.Over ⊤ T.obj₃) (s' : S.Over ⊤ T.obj₁)
      (h' : s.left ⟶ (shiftFunctor D (1 : ℤ)).obj s'.left),
      s.hom ≫ T.mor₃ = h' ≫ (shiftFunctor D (1 : ℤ)).map s'.hom →
        uZ.app s ≫ F.map h' =
          lh ≫ (shiftFunctor D' (1 : ℤ)).map (uX.app s') ≫
            (F.commShiftIso (1 : ℤ)).inv.app s'.left) :
    Nonempty ((Q ⋙ LF).mapTriangle.obj T ≅ Triangle.mk lf lg lh) := by
  classical
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  let : LF.IsRightKanExtension α := hLF
  let : NatTrans.CommShift α ℤ := hα
  obtain ⟨eX, heX⟩ := kan_value_iso F S Q LF α T.obj₁ LX hX uX huX
  obtain ⟨eY, heY⟩ := kan_value_iso F S Q LF α T.obj₂ LY hY uY huY
  obtain ⟨eZ, heZ⟩ := kan_value_iso F S Q LF α T.obj₃ LZ hZ uZ huZ
  refine ⟨Triangle.isoMk _ _ eX eY eZ ?_ ?_ ?_⟩
  · dsimp
    obtain ⟨s, r, hr, _⟩ := huY
    exact kan_value_map F S Q LF α T.mor₁ lf uX uY ⟨s, r, hr⟩ eX eY heX heY hf
  · dsimp
    obtain ⟨s, r, hr, _⟩ := huZ
    exact kan_value_map F S Q LF α T.mor₂ lg uY uZ ⟨s, r, hr⟩ eY eZ heY heZ hg
  · dsimp
    let : S.IsCompatibleWithTriangulation := hS.2
    obtain ⟨s₀, r, hr, _⟩ := huX
    let : IsSplitMono (uX.app s₀) := IsSplitMono.mk' ⟨r, hr⟩
    let v := (shiftFunctor D' (1 : ℤ)).map (uX.app s₀) ≫
      (F.commShiftIso (1 : ℤ)).inv.app s₀.left
    have hs := MorphismProperty.shift S s₀.prop (1 : ℤ)
    obtain ⟨φ, hφ⟩ := (MorphismProperty.LeftFraction.mk T.mor₃
      ((shiftFunctor D (1 : ℤ)).map s₀.hom) hs).exists_rightFraction
    let s : S.Over ⊤ T.obj₃ := MorphismProperty.Over.mk ⊤ φ.s φ.hs
    have hden : s.hom ≫ T.mor₃ = φ.f ≫ (shiftFunctor D (1 : ℤ)).map s₀.hom := hφ
    have hq : Q.map T.mor₃ ≫
        (Localization.isoOfHom Q S ((shiftFunctor D (1 : ℤ)).map s₀.hom) hs).inv =
      (Localization.isoOfHom Q S s.hom s.prop).inv ≫ Q.map φ.f := by
      apply (cancel_epi (Localization.isoOfHom Q S s.hom s.prop).hom).mp
      erw [← Category.assoc, Localization.isoOfHom_hom, ← Q.map_comp, hden, Q.map_comp]
      simp only [Category.assoc, Localization.isoOfHom_hom_inv_id, Category.comp_id]
      erw [Localization.isoOfHom_hom_inv_id_assoc]
    apply (cancel_mono v).mp
    dsimp only [v]
    simp only [Category.assoc]
    calc
      _ = LF.map (Q.map T.mor₃) ≫
          LF.map (Localization.isoOfHom Q S
            ((shiftFunctor D (1 : ℤ)).map s₀.hom) hs).inv ≫
          α.app ((shiftFunctor D (1 : ℤ)).obj s₀.left) := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun k ↦ LF.map (Q.map T.mor₃) ≫ k)
            (kan_value_shift_leg F S Q LF α eX uX heX 1 s₀ hs)
      _ = LF.map (Localization.isoOfHom Q S s.hom s.prop).inv ≫
          (Q ⋙ LF).map φ.f ≫ α.app ((shiftFunctor D (1 : ℤ)).obj s₀.left) := by
        simp only [← Category.assoc, Functor.comp_map]
        erw [← LF.map_comp, hq, LF.map_comp]
      _ = eZ.hom ≫ uZ.app s ≫ F.map φ.f := by
        erw [α.naturality, ← Category.assoc, ← heZ]
        rw [Category.assoc]
      _ = eZ.hom ≫ lh ≫ (shiftFunctor D' (1 : ℤ)).map (uX.app s₀) ≫
          (F.commShiftIso (1 : ℤ)).inv.app s₀.left := by rw [hh s s₀ φ.f hden]

end CategoryTheory.Functor

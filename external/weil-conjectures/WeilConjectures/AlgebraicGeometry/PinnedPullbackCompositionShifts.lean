/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts

/-! # Shift compatibility of the selected pullback composition comparison
Source: Stacks Project, Tags 08HY and 0D5S. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The composition comparison selected by its left-derived universal property.
Source: Stacks Project, Tag 0D5S. -/
abbrev pinnedPullbackComposition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) f g

private theorem kanPostShift
    {D D' L : Type*} [Category D] [HasShift D ℤ]
    [Category D'] [HasShift D' ℤ] [Category L] [HasShift L ℤ]
    (F : D ⥤ D') (Q : D ⥤ L)
    (LF : L ⥤ D') (α : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension α] (n : ℤ) :
    (LF ⋙ shiftFunctor D' n).IsRightKanExtension
      ((Functor.associator Q LF (shiftFunctor D' n)).inv ≫
        Functor.whiskerRight α (shiftFunctor D' n)) := by
  let P := Functor.RightExtension.postcompose₂ Q F (shiftFunctor D' n)
  let : IsIso (𝟙 (F ⋙ shiftFunctor D' n)) := by infer_instance
  let : P.IsEquivalence := by
    dsimp [P, Functor.RightExtension.postcompose₂]
    let t : ((Functor.whiskeringRight L D' D').obj (shiftFunctor D' n)) ⋙
        (Functor.whiskeringLeft D L D').obj Q ⟶
        (Functor.whiskeringLeft D L D').obj Q ⋙
          ((Functor.whiskeringRight D D' D').obj (shiftFunctor D' n)) :=
      { app G := (Functor.associator Q G (shiftFunctor D' n)).inv }
    let : IsIso t := by apply NatIso.isIso_of_isIso_app
    exact CostructuredArrow.isEquivalenceMap₂ t (𝟙 _)
  constructor
  refine ⟨Limits.IsTerminal.ofIso
    (Limits.IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension α)) ?_⟩
  exact Functor.RightExtension.postcompose₂ObjMkIso (shiftFunctor D' n) α

private theorem kanMap_commShift
    {D D' L : Type*} [Category D] [HasShift D ℤ]
    [Category D'] [HasShift D' ℤ] [Category L] [HasShift L ℤ]
    (F : D ⥤ D') [F.CommShift ℤ] (Q : D ⥤ L) [Q.CommShift ℤ]
    (LF : L ⥤ D') [LF.CommShift ℤ] (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] [NatTrans.CommShift α ℤ]
    (G : L ⥤ D') [G.CommShift ℤ] (β : Q ⋙ G ⟶ F) [NatTrans.CommShift β ℤ]
    (τ : G ⟶ LF) (hτ : Functor.whiskerLeft Q τ ≫ α = β) :
    NatTrans.CommShift τ ℤ := by
  constructor
  intro n
  let γ := (Functor.associator Q LF (shiftFunctor D' n)).inv ≫
    Functor.whiskerRight α (shiftFunctor D' n)
  let : (LF ⋙ shiftFunctor D' n).IsRightKanExtension γ := kanPostShift F Q LF α n
  apply (LF ⋙ shiftFunctor D' n).hom_ext_of_isRightKanExtension γ
  ext X
  simp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  apply (cancel_epi (G.map ((Q.commShiftIso n).hom.app X))).mp
  have fac (X : D) : τ.app (Q.obj X) ≫ α.app X = β.app X :=
    NatTrans.congr_app hτ X
  rw [← (shiftFunctor D' n).map_comp, fac]
  have hβ := NatTrans.shift_app_comm β n X
  have hα := NatTrans.shift_app_comm α n X
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hβ hα
  rw [hβ]
  have hn := τ.naturality ((Q.commShiftIso n).hom.app X)
  dsimp at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [hα, ← Category.assoc, fac]

/-- The selected pullback composition comparison commutes with the counit-compatible shifts.
Source: Stacks Project, Tag 0D5S, canonical derived pullback composition.
(blueprint: lem-pc-pinned-pullback-composition-shifts).
Proof: precompose both proposed shift equations with the localization functor Qh
and then postcompose with the selected counit of the composite pullback. The
factorization of the selected left-derived lift identifies each side with the
successive counits followed by the termwise composition comparison. The assumed
shift equations for the counits and the shift equation for termwise tensor
reassociation identify these expressions. The left-derived universal property
makes the two lifted maps equal. This proves the equation for each integer;
no cartesian, flatness or boundedness hypothesis enters. -/
theorem pinnedPullbackComposition_commShift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    (hs : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      letI := s f
      NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI := s f
    letI := s g
    letI := s (f ≫ g)
    NatTrans.CommShift (pinnedPullbackComposition.{u, w} f g).hom ℤ := by
  classical
  let := s f
  let := s g
  let := s (f ≫ g)
  have := hs f
  have := hs g
  have := hs (f ≫ g)
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) (f ≫ g)
  have := hL.isRightKanExtension
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  let β := (Functor.associator DerivedCategory.Qh (derivedPullback g)
      (derivedPullback f)).inv ≫
    Functor.whiskerRight (pinnedPullbackCounit g) (derivedPullback f) ≫
    (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
    Functor.whiskerLeft _ (pinnedPullbackCounit f) ≫
    (Functor.associator _ _
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        ((conjugateIsoEquiv
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
          (Scheme.Modules.pushforwardComp f g).symm)
        (ComplexShape.up ℤ)).hom
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  have : NatTrans.CommShift β ℤ := by dsimp only [β]; infer_instance
  dsimp only [pinnedPullbackComposition]
  rw [hc]
  exact kanMap_commShift _ DerivedCategory.Qh (derivedPullback (f ≫ g))
    (pinnedPullbackCounit (f ≫ g)) (derivedPullback g ⋙ derivedPullback f) β _
    ((derivedPullback (f ≫ g)).leftDerived_fac _ _ _ _)

end AlgebraicGeometry

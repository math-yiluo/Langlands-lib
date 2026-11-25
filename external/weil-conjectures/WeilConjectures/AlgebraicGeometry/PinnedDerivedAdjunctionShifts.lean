/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift

/-! # Shift compatibility of the selected derived adjunction
Source: Stacks Project, Tags 08HY and 0D5S. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Abelian in
private theorem canonicalRightDerivedUnitShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have hE : E.CommShift ℤ := by infer_instance
  have hU : NatTrans.CommShift E.unitIso.hom ℤ := by infer_instance
  have heq : whiskerLeft inj F.rightDerivedFunctorUnit =
      (leftUnitor G).inv ≫ whiskerRight E.unitIso.hom G ≫
        (associator E.functor E.inverse G).hom ≫
        whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_hom_app, leftUnitor_inv_app, Category.id_comp, hinv]
    simp only [Category.assoc]
    erw [Category.id_comp, Category.comp_id]
    have h := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    dsimp only [Functor.comp_map, Functor.comp_obj] at h
    change _ = (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map
      (inj.map (E.unit.app X)) ≫ _
    erw [reassoc_of% h]
    rw [← CategoryTheory.Functor.map_comp]
    change _ = _ ≫ F.rightDerivedFunctor.map
      (E.functor.map (E.unit.app X) ≫ E.counit.app (E.functor.obj X))
    erw [E.functor_unit_comp]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have : NatTrans.CommShift (whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨I, hI, i, hi, _⟩ := HasKInjectiveResolutions.exists_isKInjective P
  have := hI
  have := hi
  refine ⟨HomotopyCategory.KInjectives.mk I,
    (HomotopyCategory.quotient C (.up ℤ)).map i, ?_⟩
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map i)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) i).2 inferInstance
  dsimp only [Functor.comp_map]
  infer_instance

-- Normalization identifies the left-derived counit with the inverse mate of the right unit.

-- Normalization identifies the left-derived counit with the inverse mate of the right unit.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Abelian in
private theorem normalizedCounitShift
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    {F : C ⥤ D} {G : D ⥤ C} {LF : C' ⥤ D'} {RG : D' ⥤ C'}
    [F.CommShift ℤ] [G.CommShift ℤ] [LF.CommShift ℤ] [RG.CommShift ℤ]
    (adj : F ⊣ G) (dadj : LF ⊣ RG) [adj.CommShift ℤ] [dadj.CommShift ℤ]
    (Q : C ⥤ C') (Q' : D ⥤ D') [Q.CommShift ℤ] [Q'.CommShift ℤ]
    (ε : Q ⋙ LF ⟶ F ⋙ Q') (β : G ⋙ Q ⟶ Q' ⋙ RG) [NatTrans.CommShift β ℤ]
    (h : ∀ (M : C) (K : D) (a : F.obj M ⟶ K),
      dadj.homEquiv (Q.obj M) (Q'.obj K) (ε.app M ≫ Q'.map a) =
        Q.map (adj.homEquiv M K a) ≫ β.app K) : NatTrans.CommShift ε ℤ := by
  have hunit (M : C) : dadj.homEquiv (Q.obj M) (Q'.obj (F.obj M)) (ε.app M) =
      Q.map (adj.unit.app M) ≫ β.app (F.obj M) := by
    have hh := h M (F.obj M) (𝟙 _)
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at hh
    erw [CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id] at hh
    exact hh
  let δ := ((CategoryTheory.mateEquiv adj dadj).symm
    (TwoSquare.mk _ _ _ _ β))
  have hδ : ε = δ := by
    ext M
    apply (dadj.homEquiv _ _).injective
    erw [hunit M]
    exact CategoryTheory.unit_mateEquiv_symm adj dadj (TwoSquare.mk _ _ _ _ β) M
  rw [hδ]
  dsimp only [δ, CategoryTheory.mateEquiv, Equiv.symm, Equiv.coe_fn_mk,
    TwoSquare.mk]
  infer_instance

-- Shift equivalences preserve the Kan universal property, which detects each comparison.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open CategoryTheory.Functor CategoryTheory.Category CategoryTheory.Abelian in
private theorem rightKanShiftUnique
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (Q : C ⥤ D) (F : C ⥤ E) [Q.CommShift ℤ] [F.CommShift ℤ]
    (LF : D ⥤ E) (ε : Q ⋙ LF ⟶ F) [LF.IsRightKanExtension ε]
    (s t : LF.CommShift ℤ)
    (hs : letI := s; NatTrans.CommShift ε ℤ)
    (ht : letI := t; NatTrans.CommShift ε ℤ) : s = t := by
  have hiso (n : ℤ) : s.commShiftIso n = t.commShiftIso n := by
    let γ := (associator Q LF (shiftFunctor E n)).inv ≫
      whiskerRight ε (shiftFunctor E n)
    let P := RightExtension.postcompose₂ Q F (shiftFunctor E n)
    let : IsIso (𝟙 (F ⋙ shiftFunctor E n)) := by infer_instance
    let : P.IsEquivalence := by
      dsimp [P, RightExtension.postcompose₂]
      let δ : ((whiskeringRight D E E).obj (shiftFunctor E n)) ⋙
          (whiskeringLeft C D E).obj Q ⟶
          (whiskeringLeft C D E).obj Q ⋙
            ((whiskeringRight C E E).obj (shiftFunctor E n)) :=
        { app H := (associator Q H (shiftFunctor E n)).inv }
      let : IsIso δ := by apply NatIso.isIso_of_isIso_app
      exact CostructuredArrow.isEquivalenceMap₂ δ (𝟙 _)
    have : (LF ⋙ shiftFunctor E n).IsRightKanExtension γ := by
      constructor
      refine ⟨Limits.IsTerminal.ofIso
        (Limits.IsTerminal.isTerminalObj P _ (LF.isUniversalOfIsRightKanExtension ε)) ?_⟩
      exact RightExtension.postcompose₂ObjMkIso (shiftFunctor E n) ε
    apply Iso.ext
    apply (LF ⋙ shiftFunctor E n).hom_ext_of_isRightKanExtension γ
    ext M
    dsimp only [γ, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      associator_inv_app]
    apply (cancel_epi (LF.map ((Q.commShiftIso n).hom.app M))).mp
    have hshift (v : LF.CommShift ℤ)
        (hv : letI := v; NatTrans.CommShift ε ℤ) :
        LF.map ((Q.commShiftIso n).hom.app M) ≫
          (v.commShiftIso n).hom.app (Q.obj M) ≫ (ε.app M)⟦n⟧' =
          ε.app (M⟦n⟧) ≫ (F.commShiftIso n).hom.app M := by
      let := v
      have := hv
      simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
        NatTrans.shift_app_comm ε n M
    simpa only [Category.assoc, Category.id_comp] using (hshift s hs).trans (hshift t ht).symm
  cases s
  cases t
  congr 1
  funext n
  exact hiso n

namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

/-- The adjunction selected with the composition-pinned left-derived counit.
Source: Stacks Project, Tag 08HY, canonical derived adjunction. -/
abbrev pinnedDerivedAdjunction
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Classical.choose (exists_schemeDerivedAdjunction.{u, w} f
    (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) f)
    (pinnedPullbackCounit.{u, w} f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f))

/-- The selected derived adjunction respects the counit-compatible pullback shifts
and the recorded right-derived direct-image shifts.
Source: Stacks Project, Tag 08HY, canonical derived adjunction; Tag 079W.
(blueprint: lem-pc-pinned-derived-adjunction-shifts).
Proof: the normalization equation of exists_schemeDerivedAdjunction identifies
its Hom equivalence on localized representatives with the termwise tensor-pullback
adjunction, the selected left-derived counit and the right-derived unit. The
termwise adjunction commutes with shifts. On K-injective representatives the
right-derived unit commutes with the shift structure transported from the
K-injective equivalence. Combine this with the assumed shift equation for the
selected left-derived counit to obtain the shifted Hom-equivalence equation.
K-flat and K-injective resolutions represent every object, so naturality extends
this equation to arbitrary derived objects. Apply it to identity morphisms to
obtain the shift equations for the derived unit and counit, precisely the two
fields of Adjunction.CommShift. This concerns one morphism, independently of
any base-change square or pullback composition comparison. -/
theorem pinnedDerivedAdjunction_commShift
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    (s : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (derivedPullback.{u, w} f).CommShift ℤ)
    (hs : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      letI := s f
      NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := s f
    (pinnedDerivedAdjunction.{u, w} f).CommShift ℤ := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let adj := pinnedDerivedAdjunction.{u, w} f
  -- Keep the recorded right-derived shifts fixed and compare the two left shift structures.
  let t := adj.leftAdjointCommShift ℤ
  let := t
  have hadj : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  let a := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    |>.mapHomotopyCategory (.up ℤ)
  have ha : a.CommShift ℤ := Adjunction.CommShift.mk' a ℤ inferInstance
  let β := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
  have hβ : NatTrans.CommShift β ℤ := canonicalRightDerivedUnitShift _
  have ht : NatTrans.CommShift (pinnedPullbackCounit.{u, w} f) ℤ := by
    apply normalizedCounitShift a adj _ _
      (pinnedPullbackCounit.{u, w} f) β
    exact Classical.choose_spec (exists_schemeDerivedAdjunction.{u, w} f
      (hAdd := (Classical.choose exists_derivedPullbackComposition.{u, w}) f)
      (pinnedPullbackCounit.{u, w} f)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f))
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) f
  have := hL.isRightKanExtension
  have heq : s f = t := rightKanShiftUnique DerivedCategory.Qh _
    (derivedPullback.{u, w} f) (pinnedPullbackCounit.{u, w} f) (s f) t (hs f) ht
  have hfinal : letI := t; (pinnedDerivedAdjunction.{u, w} f).CommShift ℤ := hadj
  exact heq.symm ▸ hfinal

end AlgebraicGeometry

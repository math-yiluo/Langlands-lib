/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift

/-! # Opposite shifts and right exact derived tensor comparisons

Source: Stacks Project, Tags 06YY, 07A4 and 08JC.
(blueprint: lem-derived-right-exact-tensor-shift-cancellation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory
open scoped CategoryTheory.Functor
namespace CategoryTheory.Functor

private theorem commShift_of_fac
    {C D H : Type*} [Category C] [Category D] [Category H]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift H ℤ]
    {F₁ F₂ : C ⥤ D} [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    (τ : F₁ ⟶ F₂) (q : H ⥤ C) [q.CommShift ℤ]
    {G₁ G₂ : H ⥤ D} [G₁.CommShift ℤ] [G₂.CommShift ℤ]
    (a : q ⋙ F₁ ⟶ G₁) (b : q ⋙ F₂ ⟶ G₂) (d : G₁ ⟶ G₂)
    [NatTrans.CommShift a ℤ] [NatTrans.CommShift b ℤ] [NatTrans.CommShift d ℤ]
    (fac : Functor.whiskerLeft q τ ≫ b = a ≫ d)
    (P : H → Prop)
    (hres : ∀ X : C, ∃ Y : H, P Y ∧ Nonempty (q.obj Y ≅ X))
    (hb : ∀ Y, P Y → IsIso (b.app Y)) : NatTrans.CommShift τ ℤ where
  shift_comm n := by
    ext X
    obtain ⟨Y, hY, ⟨e⟩⟩ := hres X
    have := hb Y hY
    have hc : NatTrans.CommShift (Functor.whiskerLeft q τ ≫ b) ℤ := by
      rw [fac]
      infer_instance
    have h := NatTrans.shift_app_comm (Functor.whiskerLeft q τ ≫ b) n Y
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc] at h
    rw [← NatTrans.shift_app_comm b n Y] at h
    have hh : ((q ⋙ F₁).commShiftIso n).hom.app Y ≫
        ((Functor.whiskerLeft q τ).app Y)⟦n⟧' =
        (Functor.whiskerLeft q τ).app (Y⟦n⟧) ≫
          ((q ⋙ F₂).commShiftIso n).hom.app Y :=
      (cancel_mono ((b.app Y)⟦n⟧')).1 (by simpa only [Category.assoc] using h)
    simp only [Functor.comp_obj, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, Category.assoc] at hh
    rw [← τ.naturality_assoc] at hh
    have hY' := (cancel_epi _).1 hh
    let f := e.inv
    dsimp
    rw [← cancel_mono ((F₂.map f)⟦n⟧'), Category.assoc, ← Functor.map_comp,
      ← τ.naturality, Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc, hY',
      Category.assoc, ← Functor.commShiftIso_hom_naturality, τ.naturality_assoc]

open Abelian Limits MonoidalCategory DerivedCategory
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  Functor.mapDerivedCategory Functor.mapHomotopyCategory DerivedCategory.Qh
universe u u₁ u₂
section
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
  [BraidedCategory D] [HasFunctorialFlatResolution D] in
private theorem derived_unit_homotopy (adj : E ⊣ U)
    (X : HomotopyCategory C (.up ℤ)) :
    let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    b.unit.app (Qh.obj X) ≫ U.mapDerivedCategory.map
        (E.leftDerivedFunctorCounit.app X) ≫
      U.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj X) =
    Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) := by
  let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  have hfac := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    E.leftDerivedFunctorCounit U.rightDerivedFunctorUnit X
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc]
  erw [← U.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  erw [← Category.assoc, hfac]
  have hβ := NatTrans.congr_app U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((E.mapHomotopyCategory (.up ℤ)).obj X)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hβ
  rw [Category.assoc]
  erw [reassoc_of% hβ]
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]

-- Expanding the adjunction transpose involves several whiskered natural transformations.
omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
  [BraidedCategory D] [HasFunctorialFlatResolution D] in
private theorem derived_counit_commShift (adj : E ⊣ U) :
    let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
    letI := b.leftAdjointCommShift ℤ
    NatTrans.CommShift E.leftDerivedFunctorCounit ℤ := by
  let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  letI := b.leftAdjointCommShift ℤ
  have := b.commShift_of_rightAdjoint ℤ
  let H := E.mapHomotopyCategory (.up ℤ)
  let V := U.mapHomotopyCategory (.up ℤ)
  have hunit : NatTrans.CommShift (adj.mapHomotopyCategory (.up ℤ)).unit ℤ :=
    inferInstance
  have hfac : NatTrans.CommShift U.mapDerivedCategoryFactorsh.inv ℤ := inferInstance
  let t : Qh ⟶ (H ⋙ Qh) ⋙ U.mapDerivedCategory :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (adj.mapHomotopyCategory (.up ℤ)).unit Qh ≫
      (Functor.associator H V Qh).hom ≫
      Functor.whiskerLeft H U.mapDerivedCategoryFactorsh.inv ≫
      (Functor.associator H Qh U.mapDerivedCategory).inv
  let c : Qh ⋙ E.leftDerivedFunctor ⟶ H ⋙ Qh :=
    Functor.whiskerRight t E.leftDerivedFunctor ≫
      (Functor.associator (H ⋙ Qh) U.mapDerivedCategory E.leftDerivedFunctor).hom ≫
      Functor.whiskerLeft (H ⋙ Qh) b.counit ≫ (Functor.rightUnitor _).hom
  have hc : E.leftDerivedFunctorCounit = c := by
    ext X
    apply (b.homEquiv _ _).injective
    change b.unit.app (Qh.obj X) ≫ U.mapDerivedCategory.map
      (E.leftDerivedFunctorCounit.app X) = b.homEquiv _ _ (c.app X)
    have h := derived_unit_homotopy E U adj X
    change b.unit.app (Qh.obj X) ≫ U.mapDerivedCategory.map
        (E.leftDerivedFunctorCounit.app X) ≫
      U.mapDerivedCategoryFactorsh.hom.app (H.obj X) =
        Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) at h
    have h' : b.unit.app _ ≫ U.mapDerivedCategory.map
        (E.leftDerivedFunctorCounit.app X) = t.app X := by
      apply (cancel_mono (U.mapDerivedCategoryFactorsh.hom.app (H.obj X))).1
      simpa [t, H, V, Category.assoc] using h
    rw [h']
    have hcapp : c.app X = (b.homEquiv _ _).symm (t.app X) := by
      simp only [c, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.rightUnitor_hom_app, Category.id_comp, Adjunction.homEquiv_counit]
      erw [Category.comp_id]
    rw [hcapp, Equiv.apply_symm_apply]
  rw [hc]
  have ht : NatTrans.CommShift t ℤ := by
    dsimp only [t, H, V]
    infer_instance
  dsimp only [c]
  infer_instance

variable (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
  (LF : DerivedCategory C ⥤ DerivedCategory D) [LF.CommShift ℤ]
  (cL : Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ Qh)
  [NatTrans.CommShift cL ℤ]
  (P : HomotopyCategory C (.up ℤ) → Prop)
  (hres : ∀ K : DerivedCategory C,
    ∃ Y, P Y ∧ Nonempty (Qh.obj Y ≅ K))
  (hc : ∀ Y, P Y → IsIso (cL.app Y))
include P hres hc
-- The factorisation through `Qh` elaborates large composites of whiskered transformations.
open CategoryTheory.Functor in
/-- A natural transformation `τ : LF(Qh X ⊗ᴸ -) ⟶ LF(Qh X) ⊗ᴸ LF(-)` which is compatible, on
the homotopy category, with the comparison `F(X ⊗ -) ⟶ F(X) ⊗ F(-)`, commutes with the shifts,
if `X` and `F(X)` are K-flat. -/
private theorem commShift_of_tensorLeft_fac_models (X : HomotopyCategory C (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X)
    (hFX : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat ((F.mapHomotopyCategory (.up ℤ)).obj X))
    (hcX : IsIso (cL.app X))
    (τ : (curriedTensor (DerivedCategory C)).obj (Qh.obj X) ⋙ LF ⟶
      LF ⋙ (curriedTensor (DerivedCategory D)).obj (LF.obj (Qh.obj X)))
    (hτ : ∀ M, τ.app (Qh.obj M) ≫ cL.app X ▷ LF.obj (Qh.obj M) ≫
        Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj X) ◁ cL.app M ≫
        (tensorLeftCounit ((F.mapHomotopyCategory (.up ℤ)).obj X)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj M) =
      LF.map ((tensorLeftCounit X).app M) ≫ cL.app (X ⊗ M) ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app X).app M)) :
    NatTrans.CommShift τ ℤ := by
  let G := F.mapHomotopyCategory (.up ℤ)
  let c₂ : Qh ⋙ ((curriedTensor _).obj (Qh.obj X) ⋙ LF) ⟶
      ((curriedTensor _).obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (tensorLeftCounit X) LF ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft ((curriedTensor _).obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor _).obj X ⋙ G) ⋙ Qh ⟶ (G ⋙ (curriedTensor _).obj (G.obj X)) ⋙ Qh :=
    whiskerRight ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app X) Qh
  let c₁ : Qh ⋙ (LF ⋙ (curriedTensor _).obj (LF.obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor _).obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerLeft (Qh ⋙ LF) ((curriedTensor _).map (cL.app X)) ≫
      whiskerRight cL ((curriedTensor _).obj (Qh.obj (G.obj X))) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G (tensorLeftCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorLeftCounit (G.obj X) hFX
  have fac : whiskerLeft Qh τ ≫ c₁ = c₂ ≫ δ₀ := by
    ext M
    simpa [c₁, c₂, δ₀] using hτ M
  have := commShift_tensorLeftCounit X hX
  have := commShift_tensorLeftCounit (G.obj X) hFX
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_app F X
  have : NatTrans.CommShift δ₀ ℤ :=
    NatTrans.CommShift.whiskerRight (F₁ := (curriedTensor _).obj X ⋙ G)
      (F₂ := G ⋙ (curriedTensor _).obj (G.obj X)) _ Qh ℤ
  apply commShift_of_fac τ Qh c₂ c₁ δ₀ fac P hres
  intro Y hY
  have := hc Y hY
  dsimp only [c₁, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app]
  infer_instance

-- The factorisation through `Qh` elaborates large composites of whiskered transformations.
open CategoryTheory.Functor in
/-- A natural transformation `τ : LF(- ⊗ᴸ Qh X) ⟶ LF(-) ⊗ᴸ LF(Qh X)` which is compatible, on
the homotopy category, with the comparison `F(- ⊗ X) ⟶ F(-) ⊗ F(X)`, commutes with the shifts,
if `X` and `F(X)` are K-flat. -/
private theorem commShift_of_tensorRight_fac_models (X : HomotopyCategory C (.up ℤ))
    (hX : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X)
    (hFX : (HomotopyCategory.quasiIso D (.up ℤ)).kFlat ((F.mapHomotopyCategory (.up ℤ)).obj X))
    (hcX : IsIso (cL.app X))
    (τ : (curriedTensor (DerivedCategory C)).flip.obj (Qh.obj X) ⋙ LF ⟶
      LF ⋙ (curriedTensor (DerivedCategory D)).flip.obj (LF.obj (Qh.obj X)))
    (hτ : ∀ M, τ.app (Qh.obj M) ≫ cL.app M ▷ LF.obj (Qh.obj X) ≫
        Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj M) ◁ cL.app X ≫
        (tensorRightCounit ((F.mapHomotopyCategory (.up ℤ)).obj X)).app
          ((F.mapHomotopyCategory (.up ℤ)).obj M) =
      LF.map ((tensorRightCounit X).app M) ≫ cL.app (M ⊗ X) ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app M).app X)) :
    NatTrans.CommShift τ ℤ := by
  let G := F.mapHomotopyCategory (.up ℤ)
  let c₂ : Qh ⋙ ((curriedTensor _).flip.obj (Qh.obj X) ⋙ LF) ⟶
      ((curriedTensor _).flip.obj X ⋙ G) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (tensorRightCounit X) LF ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft ((curriedTensor _).flip.obj X) cL ≫
      (Functor.associator _ _ _).inv
  let δ₀ : ((curriedTensor _).flip.obj X ⋙ G) ⋙ Qh ⟶
      (G ⋙ (curriedTensor _).flip.obj (G.obj X)) ⋙ Qh :=
    whiskerRight ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).flipApp X) Qh
  let c₁ : Qh ⋙ (LF ⋙ (curriedTensor _).flip.obj (LF.obj (Qh.obj X))) ⟶
      (G ⋙ (curriedTensor _).flip.obj (G.obj X)) ⋙ Qh :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight cL ((curriedTensor _).flip.obj (LF.obj (Qh.obj X))) ≫
      whiskerLeft (G ⋙ Qh) ((curriedTensor _).flip.map (cL.app X)) ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft G (tensorRightCounit (G.obj X)) ≫
      (Functor.associator _ _ _).inv
  have := isIso_tensorRightCounit (G.obj X) hFX
  have fac : whiskerLeft Qh τ ≫ c₁ = c₂ ≫ δ₀ := by
    ext M
    simpa [c₁, c₂, δ₀] using hτ M
  have := commShift_tensorRightCounit X hX
  have := commShift_tensorRightCounit (G.obj X) hFX
  have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
  have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
  have := OplaxMonoidal.commShift_mapHomotopyCategoryδNatTrans_flipApp F X
  have : NatTrans.CommShift δ₀ ℤ :=
    NatTrans.CommShift.whiskerRight (F₁ := (curriedTensor _).flip.obj X ⋙ G)
      (F₂ := G ⋙ (curriedTensor _).flip.obj (G.obj X)) _ Qh ℤ
  apply commShift_of_fac τ Qh c₂ c₁ δ₀ fac P hres
  intro Y hY
  have := hc Y hY
  dsimp only [c₁, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app]
  infer_instance

omit P hres hc
section Native
variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
  [F.IsLeftAdjoint] [F.Monoidal] [F.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ]

private abbrev nativeLeft (K : DerivedCategory C) :
    tensorLeft K ⋙ F.leftDerivedFunctor ⟶
      F.leftDerivedFunctor ⋙ tensorLeft (F.leftDerivedFunctor.obj K) :=
  F.rightExact_leftDerivedTensorComparison.app K
private abbrev nativeRight (K : DerivedCategory C) :
    tensorRight K ⋙ F.leftDerivedFunctor ⟶
      F.leftDerivedFunctor ⋙ tensorRight (F.leftDerivedFunctor.obj K) :=
  F.rightExact_leftDerivedTensorComparison.flipApp K

omit [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
private theorem nativeLeft_of_iso {K K' : DerivedCategory C} (e : K ≅ K')
    [NatTrans.CommShift (nativeLeft F K') ℤ] :
    NatTrans.CommShift (nativeLeft F K) ℤ := by
  have he : nativeLeft F K =
      Functor.whiskerRight ((curriedTensor _).map e.hom) F.leftDerivedFunctor ≫
        nativeLeft F K' ≫
        Functor.whiskerLeft F.leftDerivedFunctor
          ((curriedTensor _).map (F.leftDerivedFunctor.map e.inv)) := by
    ext X
    have h := NatTrans.congr_app
      (F.rightExact_leftDerivedTensorComparison.naturality e.hom) X
    dsimp at h ⊢
    rw [reassoc_of% h, ← comp_whiskerRight, ← F.leftDerivedFunctor.map_comp,
      e.hom_inv_id, F.leftDerivedFunctor.map_id, id_whiskerRight, Category.comp_id]
  rw [he]
  infer_instance

omit [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
private theorem nativeRight_of_iso {K K' : DerivedCategory C} (e : K ≅ K')
    [NatTrans.CommShift (nativeRight F K') ℤ] :
    NatTrans.CommShift (nativeRight F K) ℤ := by
  have he : nativeRight F K =
      Functor.whiskerRight ((curriedTensor _).flip.map e.hom) F.leftDerivedFunctor ≫
        nativeRight F K' ≫
        Functor.whiskerLeft F.leftDerivedFunctor
          ((curriedTensor _).flip.map (F.leftDerivedFunctor.map e.inv)) := by
    ext X
    have h := (F.rightExact_leftDerivedTensorComparison.app X).naturality e.hom
    dsimp at h ⊢
    rw [reassoc_of% h, ← MonoidalCategory.whiskerLeft_comp,
      ← F.leftDerivedFunctor.map_comp, e.hom_inv_id, F.leftDerivedFunctor.map_id,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  rw [he]
  infer_instance

-- Constructing a common K-flat representative elaborates the flat resolution comparisons.
omit [HasFunctorialFlatResolution D] [F.PreservesKFlatQuasiIso] [F.Monoidal]
  [F.leftDerivedFunctor.CommShift ℤ] [NatTrans.CommShift F.leftDerivedFunctorCounit ℤ] in
private theorem native_models (K : DerivedCategory C) :
    ∃ X : HomotopyCategory C (.up ℤ),
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat X ∧ F.kFlatMap X ∧
        Nonempty (Qh.obj X ≅ K) := by
  obtain ⟨P, hP, _, hFP, ⟨e⟩⟩ := Functor.good_representative F K
  exact ⟨(HomotopyCategory.quotient C (.up ℤ)).obj P,
    (HomotopyCategory.kFlat_quotient_obj_iff _).2 hP,
    ObjectProperty.prop_of_iso (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomotopyCategoryFactors (.up ℤ)).app P).symm
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hFP),
    ⟨(DerivedCategory.quotientCompQhIso C).app P ≪≫ e⟩⟩

private theorem nativeLeft_commShift (K : DerivedCategory C) :
    NatTrans.CommShift (nativeLeft F K) ℤ := by
  obtain ⟨X, hX, hFX, ⟨e⟩⟩ := native_models F K
  have hc := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' X hX
  have : NatTrans.CommShift (nativeLeft F (Qh.obj X)) ℤ := by
    apply commShift_of_tensorLeft_fac_models F F.leftDerivedFunctor
      F.leftDerivedFunctorCounit
      (fun Y ↦ (HomotopyCategory.quasiIso C (.up ℤ)).kFlat Y ∧ F.kFlatMap Y)
      (fun V ↦ by
        obtain ⟨Y, hY, hFY, he⟩ := native_models F V
        exact ⟨Y, ⟨hY, hFY⟩, he⟩)
      (fun Y hY ↦ F.isIso_leftDerivedFunctorCounit_app_of_kFlat' Y hY.1)
      X hX hFX hc
    intro M
    have h := F.rightExact_leftDerivedTensorComparison_app_app_comp_tensorHom X M
    rw [MonoidalCategory.tensorHom_def, Category.assoc] at h
    exact h
  exact nativeLeft_of_iso F e.symm

private theorem nativeRight_commShift (K : DerivedCategory C) :
    NatTrans.CommShift (nativeRight F K) ℤ := by
  obtain ⟨X, hX, hFX, ⟨e⟩⟩ := native_models F K
  have hc := F.isIso_leftDerivedFunctorCounit_app_of_kFlat' X hX
  have : NatTrans.CommShift (nativeRight F (Qh.obj X)) ℤ := by
    apply commShift_of_tensorRight_fac_models F F.leftDerivedFunctor
      F.leftDerivedFunctorCounit
      (fun Y ↦ (HomotopyCategory.quasiIso C (.up ℤ)).kFlat Y ∧ F.kFlatMap Y)
      (fun V ↦ by
        obtain ⟨Y, hY, hFY, he⟩ := native_models F V
        exact ⟨Y, ⟨hY, hFY⟩, he⟩)
      (fun Y hY ↦ F.isIso_leftDerivedFunctorCounit_app_of_kFlat' Y hY.1)
      X hX hFX hc
    intro M
    have h := F.rightExact_leftDerivedTensorComparison_app_app_comp_tensorHom M X
    rw [MonoidalCategory.tensorHom_def, Category.assoc] at h
    exact h
  exact nativeRight_of_iso F e.symm
end Native
end
section CompositeShift
variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
  [T.CommShift₂Int] [S.CommShift₂Int]
  (F : C ⥤ D) [F.CommShift ℤ]
open CategoryTheory.Functor
@[instance_reducible] private def postcompose_left_commShift (K : C) :
    (((postcompose₂.obj F).obj T).obj K).CommShift ℤ :=
  inferInstanceAs ((T.obj K ⋙ F).CommShift ℤ)
@[instance_reducible] private def postcompose_right_commShift (L : C) :
    (((postcompose₂.obj F).obj T).flip.obj L).CommShift ℤ :=
  inferInstanceAs ((T.flip.obj L ⋙ F).CommShift ℤ)
@[instance_reducible] private def precompose_left_commShift (K : C) :
    (((((whiskeringLeft₂ D).obj F).obj F).obj S).obj K).CommShift ℤ :=
  inferInstanceAs ((F ⋙ S.obj (F.obj K)).CommShift ℤ)
@[instance_reducible] private def precompose_right_commShift (L : C) :
    (((((whiskeringLeft₂ D).obj F).obj F).obj S).flip.obj L).CommShift ℤ :=
  inferInstanceAs ((F ⋙ S.flip.obj (F.obj L)).CommShift ℤ)

end CompositeShift

attribute [local instance] postcompose_left_commShift postcompose_right_commShift
  precompose_left_commShift precompose_right_commShift

section Conjugate
variable {V W : Type*} [Category V] [Category W]
  [Preadditive V] [Preadditive W] [HasShift V ℤ] [HasShift W ℤ]
  [∀ n : ℤ, (shiftFunctor V n).Additive]
  [∀ n : ℤ, (shiftFunctor W n).Additive]
  [MonoidalCategory V] [MonoidalCategory W]
  [(curriedTensor V).CommShift₂Int] [(curriedTensor W).CommShift₂Int]
  (G H : V ⥤ W) [G.CommShift ℤ] [H.CommShift ℤ]
  (e : G ≅ H) [NatTrans.CommShift e.hom ℤ]
  (τ : (Functor.postcompose₂.obj H).obj (curriedTensor V) ≅
    (((Functor.whiskeringLeft₂ W).obj H).obj H).obj (curriedTensor W))

private theorem conjugate_left_commShift (K : V)
    [NatTrans.CommShift (τ.hom.app K) ℤ] :
    NatTrans.CommShift ((tensorConjugate G H e τ).hom.app K) ℤ := by
  have he : (tensorConjugate G H e τ).hom.app K =
      Functor.whiskerLeft (tensorLeft K) e.hom ≫ τ.hom.app K ≫
        Functor.whiskerLeft H ((curriedTensor W).map (e.inv.app K)) ≫
        Functor.whiskerRight e.inv (tensorLeft (G.obj K)) := by
    ext L
    simp [tensorConjugate_hom, tensorHom_def]
  rw [he]
  infer_instance

private theorem conjugate_right_commShift (K : V)
    [NatTrans.CommShift (τ.hom.flipApp K) ℤ] :
    NatTrans.CommShift ((tensorConjugate G H e τ).hom.flipApp K) ℤ := by
  have he : (tensorConjugate G H e τ).hom.flipApp K =
      Functor.whiskerLeft (tensorRight K) e.hom ≫ τ.hom.flipApp K ≫
        Functor.whiskerRight e.inv (tensorRight (H.obj K)) ≫
        Functor.whiskerLeft G ((curriedTensor W).flip.map (e.inv.app K)) := by
    ext L
    simp [tensorConjugate_hom, tensorHom_def', whisker_exchange]
  rw [he]
  infer_instance

omit [∀ n : ℤ, (shiftFunctor V n).Additive]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [MonoidalCategory V] [MonoidalCategory W]
  [Preadditive V] [Preadditive W]
  [(curriedTensor V).CommShift₂Int] [(curriedTensor W).CommShift₂Int] in
private theorem adjointUniq_commShift
    {R : W ⥤ V} [R.CommShift ℤ] (a : G ⊣ R) (b : H ⊣ R)
    [a.CommShift ℤ] [b.CommShift ℤ] :
    NatTrans.CommShift (a.leftAdjointUniq b).hom ℤ := by
  have he : (a.leftAdjointUniq b).hom =
      (Functor.leftUnitor _).inv ≫ Functor.whiskerRight b.unit G ≫
        (Functor.associator H R G).hom ≫ Functor.whiskerLeft H a.counit ≫
        (Functor.rightUnitor _).hom := by
    ext X
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    erw [Category.comp_id]
    change _ = a.homEquiv _ _ (G.map (b.unit.app X) ≫ a.counit.app _)
    rw [show (G.map (b.unit.app X) ≫ a.counit.app _) =
      (a.homEquiv _ _).symm (b.unit.app X) by
        rw [Adjunction.homEquiv_counit]]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [he]
  infer_instance
end Conjugate

section Cancellation
variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D)
  [T.CommShift₂Int] [S.CommShift₂Int]
  (F : C ⥤ D) [F.CommShift ℤ]

private def cancelTensor (K L : C) (n : ℤ) :
    (T.obj (K⟦-n⟧)).obj (L⟦n⟧) ⟶ (T.obj K).obj L :=
  ((T.flip.obj (L⟦n⟧)).commShiftIso (-n)).hom.app K ≫
    (((T.obj K).commShiftIso n).hom.app L)⟦-n⟧' ≫
    (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app _

private theorem comparison_cancellation
    (τ : (postcompose₂.obj F).obj T ⟶
      (((whiskeringLeft₂ D).obj F).obj F).obj S)
    (hleft : ∀ K, NatTrans.CommShift (τ.app K) ℤ)
    (hright : ∀ L, NatTrans.CommShift (τ.flipApp L) ℤ)
    (K L : C) (n : ℤ) :
    ((τ.app (K⟦-n⟧)).app (L⟦n⟧)) ≫
      (S.map ((F.commShiftIso (-n)).hom.app K)).app (F.obj (L⟦n⟧)) ≫
      (S.obj ((F.obj K)⟦-n⟧)).map ((F.commShiftIso n).hom.app L) ≫
      cancelTensor S (F.obj K) (F.obj L) n =
    F.map (cancelTensor T K L n) ≫ (τ.app K).app L := by
  have := hleft K
  have := hright (L⟦n⟧)
  have hL := NatTrans.shift_app_comm (τ.app K) n L
  have hR := NatTrans.shift_app_comm (τ.flipApp (L⟦n⟧)) (-n) K
  change ((T.obj K ⋙ F).commShiftIso n).hom.app L ≫
      ((τ.app K).app L)⟦n⟧' =
    (τ.app K).app (L⟦n⟧) ≫
      ((F ⋙ S.obj (F.obj K)).commShiftIso n).hom.app L at hL
  change ((T.flip.obj (L⟦n⟧) ⋙ F).commShiftIso (-n)).hom.app K ≫
      ((τ.app K).app (L⟦n⟧))⟦-n⟧' =
    (τ.app (K⟦-n⟧)).app (L⟦n⟧) ≫
      ((F ⋙ S.flip.obj (F.obj (L⟦n⟧))).commShiftIso (-n)).hom.app K at hR
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hL hR
  dsimp only [Functor.flip_obj_map] at hR
  have hN := NatTrans.shift_app_comm
    (S.flip.map ((F.commShiftIso n).hom.app L)) (-n) (F.obj K)
  simp only [Functor.flip_map_app] at hN
  dsimp only [cancelTensor]
  rw [← reassoc_of% hN]
  rw [← reassoc_of% hR]
  simp only [← Functor.map_comp_assoc]
  rw [← hL]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.commShiftIso_hom_naturality_assoc]
  have hnat := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.naturality
    ((τ.app K).app L)
  dsimp at hnat
  rw [hnat, ← F.map_shiftFunctorCompIsoId_hom_app_assoc ((T.obj K).obj L) n (-n)]
end Cancellation

section General
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

section Normalized
variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
  [F.IsLeftAdjoint] [F.Monoidal]
  (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.leftDerivedFunctor)

private theorem normalized_iso_eq
    (r : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.hom.app (DerivedCategory.Q.obj P) ≫ F.rightExact_cochainCounit P)
    (μ : ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L))
    (hμ : (∀ {K K'} (f : K ⟶ K') L,
        (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f)) ∧
      Functor.rightExactTensorModelNormalization F G r μ) :
    μ = Functor.normalizedTensorIso F G e := by
  obtain ⟨ν, hν, huniq⟩ := Functor.rightExact_tensorComparison_existsUnique F G e r hr
  have hn : Functor.rightExactTensorModelNormalization F G r
      (Functor.normalizedTensorIso F G e) := by
    intro P Q _ _ _ _
    simp only [hr]
    rw [Functor.normalizedTensorIso_inv]
    simpa only [Category.assoc] using
      transfer_tensor_counit (C := DerivedCategory C) (D := DerivedCategory D)
        G F.leftDerivedFunctor e
        (T := DerivedCategory.Q.obj (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q))
        _ _ _ _ _ _ (F.rightExact_comparison_cochain P Q)
  exact (huniq μ hμ).trans (huniq _
    ⟨Functor.normalizedTensorIso_natural₁ F G e,
      Functor.normalizedTensorIso_natural₂ F G e, hn⟩).symm
end Normalized

-- The normalization and adjoint-mate shift elaborate large derived-category comparisons.
/-- A flat-model-normalized tensor comparison for a right exact monoidal functor
commutes with cancellation of opposite shifts. The shift on the chosen derived
left adjoint is the mate of the exact right adjoint's termwise shift.
Source: Stacks 06YY, 07A4, 08JC
(blueprint: lem-derived-right-exact-tensor-shift-cancellation).

The derived counit is the transpose of the ordinary unit and thus commutes with
shifts. On good K-flat models its components are invertible. The ordinary tensor
comparison and the derived tensor counits commute with shifts, so the normalized
derived tensor comparison does too in either variable. Transport this comparison
along uniqueness of left adjoints, which also commutes with shifts. Its two shift
squares, naturality of the tensor shift, and shift coherence give cancellation. -/
private theorem rightExactTensorComparison_shiftCancellation_aux
    (adj : E ⊣ U) [E.PreservesFlat] [E.IsLeftAdjoint] [E.Monoidal]
    (G : DerivedCategory C ⥤ DerivedCategory D) (ad : G ⊣ U.mapDerivedCategory)
    (r : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = (ad.leftAdjointUniq
        (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory)).hom.app
          (DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P)
    (μ : ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L))
    (hμ : (∀ {K K'} (f : K ⟶ K') L,
        (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f)) ∧
      Functor.rightExactTensorModelNormalization E G r μ)
    (K L : DerivedCategory C) (n : ℤ) :
    letI := ad.leftAdjointCommShift ℤ
    ((G.commShiftIso (-n)).hom.app K ▷ G.obj (L⟦n⟧)) ≫
      ((G.obj K)⟦-n⟧ ◁ (G.commShiftIso n).hom.app L) ≫
      ((tensorRight ((G.obj L)⟦n⟧)).commShiftIso (-n)).hom.app (G.obj K) ≫
      (((tensorLeft (G.obj K)).commShiftIso n).hom.app (G.obj L))⟦-n⟧' ≫
      (shiftFunctorCompIsoId (DerivedCategory D) n (-n) (add_neg_cancel n)).hom.app
        (G.obj K ⊗ G.obj L) ≫ (μ K L).hom =
    (μ (K⟦-n⟧) (L⟦n⟧)).hom ≫ G.map
      (((tensorRight (L⟦n⟧)).commShiftIso (-n)).hom.app K ≫
        (((tensorLeft K).commShiftIso n).hom.app L)⟦-n⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory C) n (-n) (add_neg_cancel n)).hom.app
          (K ⊗ L)) := by
  let b := adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e := ad.leftAdjointUniq b
  letI := ad.leftAdjointCommShift ℤ
  letI := b.leftAdjointCommShift ℤ
  have := ad.commShift_of_rightAdjoint ℤ
  have := b.commShift_of_rightAdjoint ℤ
  have := derived_counit_commShift E U adj
  have := adjointUniq_commShift G E.leftDerivedFunctor ad b
  have heq := normalized_iso_eq E G e r hr μ hμ
  let τ := tensorConjugate G E.leftDerivedFunctor e
    (asIso E.rightExact_leftDerivedTensorComparison)
  have hleft (V : DerivedCategory C) : NatTrans.CommShift (τ.hom.app V) ℤ := by
    have : NatTrans.CommShift
        ((asIso E.rightExact_leftDerivedTensorComparison).hom.app V) ℤ := by
      change NatTrans.CommShift (nativeLeft E V) ℤ
      exact nativeLeft_commShift E V
    exact conjugate_left_commShift G E.leftDerivedFunctor e
      (asIso E.rightExact_leftDerivedTensorComparison) V
  have hright (V : DerivedCategory C) : NatTrans.CommShift (τ.hom.flipApp V) ℤ := by
    have : NatTrans.CommShift
        ((asIso E.rightExact_leftDerivedTensorComparison).hom.flipApp V) ℤ := by
      change NatTrans.CommShift (nativeRight E V) ℤ
      exact nativeRight_commShift E V
    exact conjugate_right_commShift G E.leftDerivedFunctor e
      (asIso E.rightExact_leftDerivedTensorComparison) V
  have hc := comparison_cancellation (curriedTensor _) (curriedTensor _) G
    τ.hom hleft hright K L n
  have hcomp (V W : DerivedCategory C) : (μ V W).inv = (τ.hom.app V).app W := by
    rw [heq]
    rfl
  apply (cancel_epi (μ (K⟦-n⟧) (L⟦n⟧)).inv).1
  apply (cancel_mono (μ K L).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  rw [hcomp, hcomp]
  exact hc

-- Converting tensor notation is done before any concrete coefficient specialization.
/-- The normalized right exact tensor comparison respects opposite-shift cancellation,
written using the tensor bifunctors. The proof is the counit/model argument above,
followed by the defining equations of the curried tensor bifunctor.
Source: Stacks 06YY, 07A4, 08JC
(blueprint: lem-derived-right-exact-tensor-shift-cancellation). -/
theorem rightExactTensorComparison_shiftCancellation
    (adj : E ⊣ U) [E.PreservesFlat] [E.IsLeftAdjoint] [E.Monoidal]
    (G : DerivedCategory C ⥤ DerivedCategory D) (ad : G ⊣ U.mapDerivedCategory)
    (r : ∀ P : CochainComplex C ℤ, G.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = (ad.leftAdjointUniq
        (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory)).hom.app
          (DerivedCategory.Q.obj P) ≫ E.rightExact_cochainCounit P)
    (μ : ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L))
    (hμ : (∀ {K K'} (f : K ⟶ K') L,
        (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f)) ∧
      Functor.rightExactTensorModelNormalization E G r μ)
    (K L : DerivedCategory C) (n : ℤ) :
    letI := ad.leftAdjointCommShift ℤ
    ((curriedTensor (DerivedCategory D)).map
        ((G.commShiftIso (-n)).hom.app K)).app (G.obj (L⟦n⟧)) ≫
      ((curriedTensor (DerivedCategory D)).obj ((G.obj K)⟦-n⟧)).map
        ((G.commShiftIso n).hom.app L) ≫
      (((((curriedTensor (DerivedCategory D)).flip.obj ((G.obj L)⟦n⟧)).commShiftIso
          (-n)).hom.app (G.obj K)) ≫
        ((((curriedTensor (DerivedCategory D)).obj (G.obj K)).commShiftIso n).hom.app
          (G.obj L))⟦-n⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory D) n (-n) (add_neg_cancel n)).hom.app
          (((curriedTensor (DerivedCategory D)).obj (G.obj K)).obj (G.obj L))) ≫
      (μ K L).hom =
    (μ (K⟦-n⟧) (L⟦n⟧)).hom ≫ G.map
      (((((curriedTensor (DerivedCategory C)).flip.obj (L⟦n⟧)).commShiftIso (-n)).hom.app K) ≫
        ((((curriedTensor (DerivedCategory C)).obj K).commShiftIso n).hom.app L)⟦-n⟧' ≫
        (shiftFunctorCompIsoId (DerivedCategory C) n (-n) (add_neg_cancel n)).hom.app
          (((curriedTensor (DerivedCategory C)).obj K).obj L)) := by
  letI := ad.leftAdjointCommShift ℤ
  simpa only [curriedTensor_map_app, curriedTensor_obj_map, curriedTensor_obj_obj,
    Category.assoc] using
    rightExactTensorComparison_shiftCancellation_aux E U adj G ad r hr μ hμ K L n

end General
end CategoryTheory.Functor

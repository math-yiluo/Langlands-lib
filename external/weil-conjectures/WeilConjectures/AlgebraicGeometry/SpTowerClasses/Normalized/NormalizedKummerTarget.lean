/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.KummerReductionUnit
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # The normalized Kummer target comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

@[reassoc]
private theorem shift_mate
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ]
    {X : C} {Y : D} (f : F.obj X ⟶ Y) (n : ℤ) :
    adj.homEquiv _ _ ((F.commShiftIso n).hom.app X ≫ f⟦n⟧') ≫
      (G.commShiftIso n).hom.app Y = (adj.homEquiv _ _ f)⟦n⟧' := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality f n]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (G.map f)⟦n⟧') (adj.shift_unit_app n X).symm

private theorem shift_add_map
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (G : D ⥤ C) [G.CommShift ℤ] (Y : D) :
    G.map ((shiftFunctorAdd D (1 : ℤ) 1).inv.app Y) ≫
        (G.commShiftIso (2 : ℤ)).hom.app Y =
      (G.commShiftIso (1 : ℤ)).hom.app (Y⟦(1 : ℤ)⟧) ≫
        ((G.commShiftIso (1 : ℤ)).hom.app Y)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd C (1 : ℤ) 1).inv.app (G.obj Y) := by
  change G.map ((shiftFunctorAdd D (1 : ℤ) 1).inv.app Y) ≫
    (G.commShiftIso ((1 : ℤ) + 1)).hom.app Y = _
  rw [G.commShiftIso_add]
  simp only [Functor.CommShift.isoAdd_hom_app, ← G.map_comp_assoc,
    Iso.inv_hom_id_app]
  rw [G.map_id, Category.id_comp]

private theorem shift_normalization
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.CommShift ℤ]
    {X : C} {Y : D} {Z : C} (c : F.obj X ≅ Y⟦(1 : ℤ)⟧)
    (d : G.obj Y ⟶ Z) (δ : X ⟶ Z⟦(1 : ℤ)⟧)
    (hc : adj.homEquiv _ _ c.hom ≫ (G.commShiftIso (1 : ℤ)).hom.app Y ≫
      d⟦(1 : ℤ)⟧' = δ) :
    ∃ b : F.obj (X⟦(1 : ℤ)⟧) ≅ Y⟦(2 : ℤ)⟧,
      adj.homEquiv _ _ b.hom ≫ (G.commShiftIso (2 : ℤ)).hom.app Y ≫
        d⟦(2 : ℤ)⟧' = δ⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd C (1 : ℤ) 1).inv.app Z := by
  let := adj.leftAdjointCommShift ℤ
  let := adj.commShift_of_rightAdjoint ℤ
  let b : F.obj (X⟦(1 : ℤ)⟧) ≅ Y⟦(2 : ℤ)⟧ :=
    (F.commShiftIso (1 : ℤ)).app X ≪≫ (shiftFunctor D (1 : ℤ)).mapIso c ≪≫
      ((shiftFunctorAdd D (1 : ℤ) 1).app Y).symm
  refine ⟨b, ?_⟩
  have hb : b.hom =
      ((F.commShiftIso (1 : ℤ)).hom.app X ≫ c.hom⟦(1 : ℤ)⟧') ≫
        (shiftFunctorAdd D (1 : ℤ) 1).inv.app Y := by
    simp only [b, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, Category.assoc]
  have hb' : adj.homEquiv _ _ b.hom ≫ (G.commShiftIso (2 : ℤ)).hom.app Y =
      (adj.homEquiv _ _ c.hom ≫ (G.commShiftIso (1 : ℤ)).hom.app Y)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd C (1 : ℤ) 1).inv.app (G.obj Y) := by
    rw [hb, adj.homEquiv_naturality_right]
    simp only [Category.assoc]
    rw [shift_add_map, shift_mate_assoc adj c.hom (1 : ℤ)]
    simp only [Functor.map_comp, Category.assoc]
  have hd := (shiftFunctorAdd C (1 : ℤ) 1).inv.naturality d
  change d⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd C (1 : ℤ) 1).inv.app Z =
    (shiftFunctorAdd C (1 : ℤ) 1).inv.app (G.obj Y) ≫ d⟦(2 : ℤ)⟧' at hd
  rw [← Category.assoc, hb', Category.assoc, ← hd]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ z⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd C (1 : ℤ) 1).inv.app Z) hc

private structure TargetNormalizationData
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension F G) {X₁ X₂ X₃ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0)
    (hs : (ShortComplex.mk f g hfg).ShortExact)
    (M : D) (i : G.obj M ≅ X₁) where
  comparison : r.derived.obj (((DerivedCategory.singleFunctor C 0).obj X₃)⟦(1 : ℤ)⟧) ≅
    ((DerivedCategory.singleFunctor D 0).obj M)⟦(2 : ℤ)⟧
  normalization : r.targetNormalization (ShortComplex.mk f g hfg) hs comparison i

private theorem derived_target_normalization
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension F G) {X₁ X₂ X₃ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0)
    (hs : (ShortComplex.mk f g hfg).ShortExact)
    (M : D) (i : G.obj M ≅ X₁)
    (c : r.derived.obj ((DerivedCategory.singleFunctor C 0).obj X₃) ≅
      ((DerivedCategory.singleFunctor D 0).obj M)⟦(1 : ℤ)⟧)
    (hc : r.derivedAdjunction.homEquiv _ _ c.hom ≫
      (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor D 0).obj M) ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor C 0).map i.hom)⟦(1 : ℤ)⟧' = hs.singleδ) :
    Nonempty (TargetNormalizationData r f g hfg hs M i) := by
  let d := (G.mapDerivedCategorySingleFunctor 0).hom.app M ≫
    (DerivedCategory.singleFunctor C 0).map i.hom
  have hc' : r.derivedAdjunction.homEquiv _ _ c.hom ≫
      (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor D 0).obj M) ≫
      d⟦(1 : ℤ)⟧' = hs.singleδ := by
    simpa only [d, Functor.map_comp, Category.assoc] using hc
  obtain ⟨b, hb⟩ := shift_normalization r.derivedAdjunction c d hs.singleδ hc'
  refine ⟨⟨b, ?_⟩⟩
  simpa only [DerivedExtension.targetNormalization, d, Functor.map_comp,
    Category.assoc] using hb

private theorem normalize_targets
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension F G) {X₁ X₂ X₃ : C}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : f ≫ g = 0)
    (hs : (ShortComplex.mk f g hfg).ShortExact)
    (h : ∃ (M : D) (i : G.obj M ≅ X₁)
      (c : r.derived.obj ((DerivedCategory.singleFunctor C 0).obj X₃) ≅
        ((DerivedCategory.singleFunctor D 0).obj M)⟦(1 : ℤ)⟧),
      r.derivedAdjunction.homEquiv _ _ c.hom ≫
        (G.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor D 0).obj M) ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app M)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor C 0).map i.hom)⟦(1 : ℤ)⟧' = hs.singleδ) :
    ∃ (M : D) (i : G.obj M ≅ X₁)
      (b : r.derived.obj (((DerivedCategory.singleFunctor C 0).obj X₃)⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor D 0).obj M)⟦(2 : ℤ)⟧),
      r.targetNormalization (ShortComplex.mk f g hfg) hs b i := by
  obtain ⟨M, i, c, hc⟩ := h
  obtain ⟨data⟩ := derived_target_normalization r f g hfg hs M i c hc
  exact ⟨M, i, data.comparison, data.normalization⟩

/-- Shift the unshifted Kummer comparison, preserving its positive boundary adjunct.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2);
expanded `SmoothPurityTowerClasses`, steps 3--7.
(blueprint: lem-sfb-normalized-kummer-target).

Proof: obtain the roots module and its once-shifted comparison from the unshifted
Kummer computation. The adjunction to exact forgetting induces a coherent shift
structure on the derived extension. Shift its comparison once, prepend the
extension's shift comparison, and collapse the two target shifts by the inverse
of shiftFunctorAdd. The adjunction-unit shift identity identifies the adjunct
of the shifted comparison; commShiftIso_add identifies its composite with the
forgetful shift comparison. Naturality of shiftFunctorAdd with the single-functor
comparison followed by the roots isomorphism gives targetNormalization with
exactly the positive boundary and specified shift-addition map. These are
identities in the entire derived system category, without evaluation. -/
theorem exists_normalizedKummerTarget (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (k : Kummer l T)
    (r : Reduction T (Rrings l T)) :
    ∃ (M : Systems T (Rrings l T)) (i : r.forget.F.obj M ≅ roots l T)
      (b : r.derived.obj (((DerivedCategory.singleFunctor (Ab T) 0).obj
        (units T))⟦(1 : ℤ)⟧) ≅
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj M)⟦(2 : ℤ)⟧),
      r.model.targetNormalization (ShortComplex.mk k.inclusion k.power k.zero)
        k.exact b i := by
  exact normalize_targets r.model k.inclusion k.power k.zero k.exact
    (exists_kummerReductionUnit l T hT k r)

end AlgebraicGeometry.ProEtale.SpTowerClasses

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluationEquation
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj

/-! # Exact lifting of evaluated derived arrows -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe wC wB wD
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.homEquiv Ext.comp
  Ext.mk₀ Ext.mapExactFunctor

private theorem lift_ext
    {C B D : Type*} [Category C] [Category B] [Category D]
    [Abelian C] [Abelian B] [Abelian D]
    [HasExt.{wC} C] [HasExt.{wB} B] [HasExt.{wD} D]
    (G : C ⥤ B) (S : B ⥤ D) (V : C ⥤ D)
    [G.Additive] [S.Additive] [V.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [S.Full] [S.Faithful] (e : G ⋙ S ≅ V)
    {X Y : C} {P Q : B} (a : V.obj X ≅ S.obj P) (b : V.obj Y ≅ S.obj Q)
    (x : Ext.{wC} X Y 2) :
    ∃ y : Ext.{wB} P Q 2,
      y.mapExactFunctor S = Ext.mk₀CompMk₀ a.inv (x.mapExactFunctor V) b.hom := by
  let a' := S.preimageIso (e.app X ≪≫ a)
  let b' := S.preimageIso (e.app Y ≪≫ b)
  refine ⟨Ext.mk₀CompMk₀ a'.inv (x.mapExactFunctor G) b'.hom, ?_⟩
  rw [Ext.mapExactFunctor_mk₀CompMk₀]
  have hs := Ext.mapExactFunctor_comp_mk₀_eq_sheaf G S V e.symm x
  have ht : (x.mapExactFunctor G).mapExactFunctor S =
      Ext.mk₀CompMk₀ (e.hom.app X) (x.mapExactFunctor V) (e.inv.app Y) := by
    apply_fun (fun z ↦ (Ext.mk₀ (e.hom.app X)).comp z (zero_add 2)) at hs
    simpa only [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id_app, Ext.mk₀_id_comp, Iso.symm_hom,
      Ext.mk₀CompMk₀] using hs.symm
  rw [ht, Ext.mk₀CompMk₀_mk₀CompMk₀]
  simp only [a', b', Functor.preimageIso_inv, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Iso.inv_hom_id_app_assoc]

private theorem nested_ext_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{wC} C] [HasExt.{wD} D] [HasExt.{wB} (ℕᵒᵖ ⥤ D)]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ (ℕᵒᵖ ⥤ D)) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {P Q : D} (n : ℕ) (a : (F.obj X).obj (op n) ≅ P)
    (b : (F.obj Y).obj (op n) ≅ Q) (x : Ext.{wC} X Y 2) :
    (Ext.mk₀CompMk₀ a.inv
      ((x.mapExactFunctor F).mapExactFunctor
        ((evaluation ℕᵒᵖ D).obj (op n))) b.hom).hom =
    (supportedFiniteSingleCoordinates F X n a).inv ≫
      (((evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory).map
        (F.mapDerivedCategory.map x.hom) ≫
      (supportedFiniteShiftedCoordinates F Y n b).hom := by
  simp only [Ext.mk₀CompMk₀, Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map,
    supportedFiniteSingleCoordinates, supportedFiniteShiftedCoordinates,
    Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.app_inv, Iso.app_hom, Functor.map_comp, Category.assoc, Nat.cast_ofNat]
  erw [Functor.commShiftIso_hom_naturality_assoc]

/-- An exact lift of evaluation and fully faithful scalar restriction lift any derived arrow.
Source: exact Ext functoriality and single/shift comparison naturality
(blueprint: lem-sfb-diagonal-trace-exact-finite-evaluation-lift).

Proof: express the arrow as an Ext class; apply the exact lifting functor; lift the two
endpoint isomorphisms through the fully faithful restriction; and transport the Ext class.
The exact-functor composition formula identifies its restricted image. Ext hom, the single
comparisons and shift naturality give precisely the finiteEvaluationEquation property. -/
theorem exactFiniteEvaluation_lift
    {C B D : Type*} [Category C] [Category B] [Category D]
    [Abelian C] [Abelian B] [Abelian D]
    [HasExt.{wC} C] [HasExt.{wB} B] [HasExt.{wD} D]
    [HasExt.{wB} (ℕᵒᵖ ⥤ D)]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ (ℕᵒᵖ ⥤ D)) (G : C ⥤ B) (S : B ⥤ D)
    [F.Additive] [G.Additive] [S.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [S.Full] [S.Faithful] (n : ℕ)
    (e : G ⋙ S ≅ F ⋙ (evaluation ℕᵒᵖ D).obj (op n))
    {X Y : C} {P Q : B} (a : (F.obj X).obj (op n) ≅ S.obj P)
    (b : (F.obj Y).obj (op n) ≅ S.obj Q)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :
    ∃ y : Ext.{wB} P Q 2, finiteEvaluationEquation F S n a b f y := by
  let ev := (evaluation ℕᵒᵖ D).obj (op n)
  let x : Ext.{wC} X Y 2 := Ext.homEquiv.symm f
  have hx : x.hom = f := Ext.homEquiv.apply_symm_apply _
  obtain ⟨y, hy⟩ := lift_ext G S (F ⋙ ev) e a b x
  refine ⟨y, ?_⟩
  unfold finiteEvaluationEquation
  rw [hy]
  have hc := Ext.mapExactFunctor_comp_mk₀_eq_sheaf F ev (F ⋙ ev) (Iso.refl _) x
  simp only [Iso.refl_hom, NatTrans.id_app, Ext.comp_mk₀_id, Ext.mk₀_id_comp] at hc
  rw [hc, nested_ext_hom, hx]

end AlgebraicGeometry.ProEtale.DiagonalTrace

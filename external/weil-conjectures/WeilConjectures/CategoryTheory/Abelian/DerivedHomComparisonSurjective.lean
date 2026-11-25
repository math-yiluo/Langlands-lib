/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedHom
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Category.Grp.Zero

/-! # Surjectivity of a derived Hom comparison by effacement

Source: Stacks Project, Tag 03FD, acyclic-resolution argument.
(blueprint: lem-sbc-derived-hom-comparison-surjective).
-/

@[expose] public section

universe w w' v v' u u'
open CategoryTheory Limits Abelian Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem extComparison_surjective
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : C) (B : D) (a : B ⟶ F.obj L)
    (hzero : ∀ N : C, Function.Surjective (fun f : L ⟶ N ↦ a ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I] (n : ℕ),
      Subsingleton (Ext.{w'} B (F.obj I) (n + 1))) (N : C) (n : ℕ) :
    Function.Surjective (fun x : Ext.{w} L N n ↦
      (Ext.mk₀ a).comp (x.mapExactFunctor F) (zero_add n)) := by
  induction n generalizing N with
  | zero =>
    intro y
    obtain ⟨f, hf⟩ := hzero N (Ext.homEquiv₀ y)
    refine ⟨Ext.mk₀ f, ?_⟩
    simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀,
      hf, Ext.mk₀_homEquiv₀_apply]
  | succ n ih =>
    let I : InjectivePresentation N := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have : Injective S.X₂ := I.injective
    have : Subsingleton (Ext.{w'} B (S.map F).X₂ (n + 1)) := hacyclic S.X₂ n
    intro y
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁.{w'} B (hS.map F) y
      (Subsingleton.elim _ _) rfl
    obtain ⟨x, hx⟩ := ih S.X₃ z
    refine ⟨x.comp hS.extClass rfl, ?_⟩
    dsimp only at hx ⊢
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
    rw [← Ext.comp_assoc (Ext.mk₀ a) (x.mapExactFunctor F)
      (hS.map F).extClass (zero_add n) rfl (by omega), hx]
    exact hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An exact functor gives a surjective fixed-source derived Hom comparison if the
ordinary Hom comparison is surjective and images of injectives are acyclic for Hom
from the fixed target source.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: lem-sbc-derived-hom-comparison-surjective).

Proof: In degree zero use the fully faithful single functor and hzero. For degree
n+1 embed the coefficient N into an injective I and form its cokernel Q. Exactness
of F preserves this short exact sequence. Acyclicity makes the connecting map from
Ext^n(B,F(Q)) onto Ext^(n+1)(B,F(N)) surjective. Lift an abelian class through this
connecting map, then lift its preimage using the induction hypothesis for Q.
Apply the module connecting map to this lift. Exact functors preserve extension
classes, and associativity of Yoneda composition proves that its image is the
original class. The fully faithful inclusion of D+ into D and the single/shift
comparisons identify this Ext calculation with the displayed map. -/
theorem derivedHomComparison_surjective
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory D] [HasExt.{v'} D] [EnoughInjectives D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : C) (B : D) (a : B ⟶ F.obj L)
    (hzero : ∀ N : C, Function.Surjective (fun f : L ⟶ N ↦ a ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I],
      (preadditiveCoyoneda.obj (op B)).rightAcyclic (F.obj I)) (N : C) (n : ℕ) :
    Function.Surjective (fun x :
      (DerivedCategory.Plus.singleFunctor C 0).obj L ⟶
        ((DerivedCategory.Plus.singleFunctor C 0).obj N)⟦(n : ℤ)⟧ ↦
      (DerivedCategory.Plus.singleFunctor D 0).map a ≫
        (F.mapDerivedCategoryPlusSingleFunctor 0).inv.app L ≫
        F.mapDerivedCategoryPlus.map x ≫
        (F.mapDerivedCategoryPlus.commShiftIso (n : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj N) ≫
        (shiftFunctor _ (n : ℤ)).map
          ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app N)) := by
  intro y
  let jC := (DerivedCategory.Plus.ι (C := C)).commShiftIso (n : ℤ)
  let jD := (DerivedCategory.Plus.ι (C := D)).commShiftIso (n : ℤ)
  let z : Ext.{v'} B (F.obj N) n := Ext.homEquiv.symm
    (y.hom ≫ jD.hom.app ((DerivedCategory.Plus.singleFunctor D 0).obj (F.obj N)))
  have hacExt (I : C) [Injective I] (k : ℕ) :
      Subsingleton (Ext.{v'} B (F.obj I) (k + 1)) := by
    obtain ⟨eExt⟩ := nonempty_extFunctor_iso_rightDerivedHom B (k + 1)
    exact AddCommGrpCat.subsingleton_of_isZero
      ((hacyclic I k).of_iso (eExt.app (F.obj I)))
  obtain ⟨x, hx⟩ := extComparison_surjective F L B a hzero hacExt N n z
  let t : (DerivedCategory.Plus.singleFunctor C 0).obj L ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj N)⟦(n : ℤ)⟧ :=
    ObjectProperty.homMk (x.hom ≫ jC.inv.app ((DerivedCategory.Plus.singleFunctor C 0).obj N))
  refine ⟨t, ?_⟩
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono (jD.hom.app _)).1
  dsimp only [jC, jD]
  simp only [Functor.map_comp, Category.assoc]
  have hinv : DerivedCategory.Plus.ι.map
      ((F.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) =
      (F.mapDerivedCategorySingleFunctor 0).inv.app L := by
    apply (cancel_mono ((F.mapDerivedCategorySingleFunctor 0).hom.app L)).1
    rw [← F.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
      ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
    rw [F.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app, Iso.inv_hom_id_app]
    rfl
  rw [hinv]
  have hn := ((DerivedCategory.Plus.ι (C := D)).commShiftIso (n : ℤ)).hom.naturality
    ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app N)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  rw [F.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  have hs := F.ι_map_mapDerivedCategoryPlus_commShiftIso_hom_app (n : ℤ)
    ((DerivedCategory.Plus.singleFunctor C 0).obj N)
  erw [reassoc_of% hs]
  have hh := congrArg (fun e : Ext.{v'} B (F.obj N) n ↦ e.hom) hx
  change (DerivedCategory.singleFunctor D 0).map a ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app L ≫
    F.mapDerivedCategory.map
      (x.hom ≫ jC.inv.app ((DerivedCategory.Plus.singleFunctor C 0).obj N)) ≫
    F.mapDerivedCategory.map
      (jC.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj N)) ≫
    (F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app
      ((DerivedCategory.singleFunctor C 0).obj N) ≫
    (shiftFunctor _ (n : ℤ)).map
      ((F.mapDerivedCategorySingleFunctor 0).hom.app N) = _
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapDerivedCategory.map_comp_assoc (jC.inv.app _)
    (jC.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj N)),
    jC.inv_hom_id_app, Functor.map_id, Category.id_comp]
  dsimp only at hh
  dsimp only [z] at hh
  simp only [Ext.comp_hom, Ext.mapExactFunctor_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.map,
    Equiv.apply_symm_apply, Category.assoc] at hh
  exact hh

-- Keep the comparison bundled while cancelling a coefficient isomorphism.
-- This prevents concrete sheaf functor instances from being repeatedly expanded.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem derivedHomComparison_surjective_postcomp
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory D] [HasExt.{v'} D] [EnoughInjectives D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : C) (B : D) (a : B ⟶ F.obj L)
    (hzero : ∀ N : C, Function.Surjective (fun f : L ⟶ N ↦ a ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I],
      (preadditiveCoyoneda.obj (op B)).rightAcyclic (F.obj I)) (N : C) (n : ℕ)
    (N' : D) (e : F.obj N ⟶ N') [IsIso e] :
    Function.Surjective
      (((Preadditive.leftComp _
        ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
          (F.mapDerivedCategoryPlusSingleFunctor 0).inv.app L)).comp
        (Preadditive.rightComp _
          ((F.mapDerivedCategoryPlus.commShiftIso (n : ℤ)).hom.app
              ((DerivedCategory.Plus.singleFunctor C 0).obj N) ≫
            (shiftFunctor _ (n : ℤ)).map
              ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app N ≫
                (DerivedCategory.Plus.singleFunctor D 0).map e)))).comp
        F.mapDerivedCategoryPlus.mapAddHom) := by
  have hs := derivedHomComparison_surjective F L B a hzero hacyclic N n
  let d := (shiftFunctor _ (n : ℤ)).map
    ((DerivedCategory.Plus.singleFunctor D 0).map e)
  have : IsIso d := by dsimp only [d]; infer_instance
  intro y
  obtain ⟨x, hx⟩ := hs (y ≫ inv d)
  refine ⟨x, ?_⟩
  change ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
      (F.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) ≫
    (F.mapDerivedCategoryPlus.map x ≫
      ((F.mapDerivedCategoryPlus.commShiftIso (n : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj N) ≫
        (shiftFunctor _ (n : ℤ)).map
          ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app N ≫
            (DerivedCategory.Plus.singleFunctor D 0).map e))) = y
  have hx' := congrArg (fun z ↦ z ≫ d) hx
  simpa only [d, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
    Functor.map_comp] using hx'


end CategoryTheory

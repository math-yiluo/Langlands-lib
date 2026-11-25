/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedHom
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import all WeilConjectures.CategoryTheory.DerivedSourceComparisonExtCompatibility
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.FiveLemma

/-! # Detecting derived classes through an acyclic source comparison

Source: Stacks Project, Tags 03FD and 015E, acyclic-resolution argument.
(blueprint: lem-sbc-derived-source-comparison-injective).
-/

@[expose] public section

universe v u₁ u₂
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace CategoryTheory

private theorem sourceHom_bijective
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L)
    (hhom : ∀ (I : C), Injective I →
      Function.Bijective (fun f : L ⟶ I ↦ a ≫ V.map f)) (Y : C) :
    Function.Bijective (fun f : L ⟶ Y ↦ a ≫ V.map f) := by
  classical
  let I : InjectivePresentation Y := Classical.arbitrary _
  have := I.injective
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  let J : InjectivePresentation S.X₃ := Classical.arbitrary _
  have := J.injective
  constructor
  · intro f g hfg
    apply (cancel_mono I.f).1
    apply (hhom I.J inferInstance).1
    dsimp only at hfg
    simpa only [V.map_comp, ← Category.assoc] using
      congrArg (fun t ↦ t ≫ V.map I.f) hfg
  · intro g
    obtain ⟨f, hf⟩ := (hhom I.J inferInstance).2 (g ≫ V.map I.f)
    dsimp only at hf
    have hz : f ≫ S.g ≫ J.f = 0 := by
      apply (hhom J.J inferInstance).1
      change a ≫ V.map (f ≫ S.g ≫ J.f) = a ≫ V.map 0
      simp only [V.map_comp, V.map_zero, comp_zero]
      rw [← Category.assoc a, hf]
      change (g ≫ V.map S.f) ≫ V.map S.g ≫ V.map J.f = 0
      rw [Category.assoc g, ← V.map_comp_assoc, S.zero, V.map_zero]
      simp
    have hfz : f ≫ S.g = 0 := by
      apply (cancel_mono J.f).1
      simpa using hz
    obtain ⟨k, hk⟩ := hS.exact.lift' f hfz
    refine ⟨k, ?_⟩
    apply (cancel_mono (V.map I.f)).1
    change k ≫ I.f = f at hk
    rw [Category.assoc, ← V.map_comp, hk]
    exact hf

private lemma sourceExtMap_comp
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L) {Y Z : C} {q r : ℕ}
    (x : Abelian.Ext L Y q) (z : Abelian.Ext Y Z r) :
    sourceExtMap V L B a Z (q + r) (x.comp z rfl) =
      (sourceExtMap V L B a Y q x).comp (z.mapExactFunctor V) rfl := by
  dsimp [sourceExtMap]
  rw [Abelian.Ext.mapExactFunctor_comp]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem sourceExtMap_bijective
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
    [HasExt.{v} C] [HasExt.{v} D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L)
    (hhom : ∀ (I : C), Injective I →
      Function.Bijective (fun f : L ⟶ I ↦ a ≫ V.map f))
    (hac : ∀ (I : C), Injective I →
      (preadditiveCoyoneda.obj (Opposite.op B)).rightAcyclic (V.obj I))
    (Y : C) (q : ℕ) : Function.Bijective (sourceExtMap V L B a Y q) := by
  classical
  have hzero (I : C) [Injective I] (n : ℕ) (x : Abelian.Ext B (V.obj I) (n + 1)) :
      x = 0 := by
    obtain ⟨e⟩ := nonempty_extFunctor_iso_rightDerivedHom B (n + 1)
    have hz := (hac I inferInstance n).of_iso (e.app (V.obj I))
    exact (AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim x 0
  induction q generalizing Y with
  | zero =>
    have hmk (f : L ⟶ Y) : sourceExtMap V L B a Y 0 (Abelian.Ext.mk₀ f) =
        Abelian.Ext.mk₀ (a ≫ V.map f) := by
      dsimp [sourceExtMap]
      simp [Abelian.Ext.mapExactFunctor_mk₀,
        Abelian.Ext.mk₀_comp_mk₀]
    constructor
    · intro x y hxy
      obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
      obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
      rw [hmk, hmk] at hxy
      rw [(sourceHom_bijective V L B a hhom Y).1
        ((Abelian.Ext.mk₀_bijective _ _).1 hxy)]
    · intro z
      obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 z
      obtain ⟨f, hf⟩ := (sourceHom_bijective V L B a hhom Y).2 g
      exact ⟨Abelian.Ext.mk₀ f, (hmk f).trans (congrArg Abelian.Ext.mk₀ hf)⟩
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    have := I.injective
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hT : (S.map V).ShortExact := hS.map_of_exact V
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Abelian.Ext.mk₀ S.g).postcomp L (add_zero n)) (hS.extClass.postcomp L rfl)
      ((Abelian.Ext.mk₀ (V.map S.g)).postcomp B (add_zero n))
      (hT.extClass.postcomp B rfl)
      (sourceExtMap V L B a I.J n) (sourceExtMap V L B a S.X₃ n)
      (sourceExtMap V L B a Y (n + 1))
      (AddMonoidHom.ext fun x ↦ by
        change (sourceExtMap V L B a I.J n x).comp
          (Abelian.Ext.mk₀ (V.map S.g)) (add_zero n) =
          sourceExtMap V L B a S.X₃ n (x.comp (Abelian.Ext.mk₀ S.g) (add_zero n))
        simpa only [Abelian.Ext.mapExactFunctor_mk₀, Nat.add_zero,
          AddMonoidHom.comp_apply] using
          (sourceExtMap_comp V L B a x (Abelian.Ext.mk₀ S.g)).symm)
      (AddMonoidHom.ext fun x ↦ by
        change (sourceExtMap V L B a S.X₃ n x).comp hT.extClass rfl =
          sourceExtMap V L B a Y (n + 1) (x.comp hS.extClass rfl)
        simpa only [Abelian.Ext.mapExactFunctor_extClass, AddMonoidHom.comp_apply] using
          (sourceExtMap_comp V L B a x hS.extClass).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' L hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' B hT n (n + 1) rfl))
      (hn I.J).2 (hn S.X₃)
      (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ _ hS x
        (Abelian.Ext.eq_zero_of_injective (I := I.J) _) rfl)
      (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ _ hT x
        (hzero I.J n _) rfl)

/-- Termwise Hom comparison and acyclicity detect derived classes.
Source: Stacks Project, Tag 03FD, first and second proof paragraphs; Tag 015E.
(blueprint: lem-sbc-derived-source-comparison-injective).

Proof: Choose an injective resolution I of Y in C. Exactness of V makes V(I)
an exact resolution of V(Y). Its terms are acyclic for Hom(B,-) by hac.
Consequently Hom(B,V(I)) computes derived Hom(B,V(Y)), by the acyclic-resolution
comparison. The maps f ↦ a ≫ V(f) commute with differentials by functoriality
and associativity. Their bijectivity on injectives makes Hom(L,I) and
Hom(B,V(I)) isomorphic complexes of abelian groups. In particular their
cohomology maps are injective. The injective-resolution realization identifies
Hom(L[0],Y[0][q]) with the first cohomology group. The augmentation-compatible
acyclic-resolution realization identifies the second with
Hom(B[0],V(Y)[0][q]). Mapping a cocycle through V and precomposing by a[0]
gives precisely the displayed map: the inverse single comparison identifies
V(L[0]) with V(L)[0], and the augmentation commutes with V. Hence the displayed
map is injective before any coefficient identification. This argument also
covers degree zero and zero objects; no preservation of injectives by V is used. -/
theorem derivedSourceComparison_injective
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (V : C ⥤ D) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : C) (B : D) (a : B ⟶ V.obj L)
    (hhom : ∀ (I : C), Injective I →
      Function.Bijective (fun f : L ⟶ I ↦ a ≫ V.map f))
    (hac : ∀ (I : C), Injective I →
      (preadditiveCoyoneda.obj (Opposite.op B)).rightAcyclic (V.obj I))
    (Y : C) (q : ℕ) :
    Function.Injective (fun x : (DerivedCategory.Plus.singleFunctor C 0).obj L ⟶
        ((DerivedCategory.Plus.singleFunctor C 0).obj Y)⟦(q : ℤ)⟧ ↦
      ((DerivedCategory.Plus.singleFunctor D 0).map a ≫
        (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L) ≫
        V.mapDerivedCategoryPlus.map x) := by
  let : HasExt.{v} C := hasExt_of_enoughInjectives.{v} C
  let : HasExt.{v} D := hasExt_of_enoughInjectives.{v} D
  intro x y hxy
  let iC := DerivedCategory.Plus.ι (C := C)
  let ex : Abelian.Ext.{v} L Y q :=
    Abelian.Ext.homEquiv.symm (ShiftedHom.map x iC)
  let ey : Abelian.Ext.{v} L Y q :=
    Abelian.Ext.homEquiv.symm (ShiftedHom.map y iC)
  have he := derivedSourceComparison_ext_compatibility V L B a Y q x y hxy
  have := (sourceExtMap_bijective V L B a hhom hac Y q).1 he
  apply iC.map_injective
  apply (cancel_mono ((iC.commShiftIso (q : ℤ)).hom.app
    ((DerivedCategory.Plus.singleFunctor C 0).obj Y))).1
  have hh := congrArg Abelian.Ext.homEquiv this
  rw [Equiv.apply_symm_apply,
    Equiv.apply_symm_apply] at hh
  exact hh

end CategoryTheory

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The internal hom of modules over a commutative monoid, concretely

Let `A` be a commutative monoid in a symmetric monoidal closed category `C` with equalizers and
coequalizers. For `A`-modules `M` and `N`, the internal hom `[M, N]` of `C` is an `A`-module
through `N` (`CategoryTheory.Mod.homMod`), and the `A`-linear maps form the equalizer
`Hom_A(M, N)` of
```
  [M, N] ⇉ [A ⊗ M, N],   f ↦ f ∘ act_M,   f ↦ act_N ∘ (A ⊗ f)
```
(`CategoryTheory.Mod.ihom'`). It is right adjoint to the tensor product `- ⊗_A M`
(`CategoryTheory.Mod.ihom'Adjunction`). Unlike the abstract right adjoint
`CategoryTheory.Mod.ihom`, its underlying object is computed in `C`, which makes it possible to
compare it along functors preserving internal homs and equalizers: for a lax braided functor
`F` with `F [Z, Y] ≅ [F Z, F Y]` and a monoid isomorphism `ρ : B ≅ F A`, the comparison
`F Hom_A(M, N) ⟶ Hom_B(F M, F N)` (`CategoryTheory.Mod.mapIhom'Hom`) is an isomorphism as
soon as `F` preserves the defining equalizer (`CategoryTheory.Mod.isIso_mapIhom'Hom`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj MonoidalClosed Limits

namespace CategoryTheory.Mod

variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {A : C} [MonObj A]

variable (A) in
/-- The action `(a · f)(z) = a · f(z)` of `A` on `[Z, N]` through an `A`-module `N`. -/
def homAct (Z : C) (N : Mod C A) :
    A ⊗ (CategoryTheory.ihom Z).obj N.X ⟶ (CategoryTheory.ihom Z).obj N.X :=
  curry ((α_ Z A _).inv ≫ (β_ Z A).hom ▷ _ ≫ (α_ A Z _).hom ≫
    A ◁ (CategoryTheory.ihom.ev Z).app N.X ≫ act N.X)

lemma uncurry_homAct (Z : C) (N : Mod C A) :
    uncurry (homAct A Z N) = (α_ Z A _).inv ≫ (β_ Z A).hom ▷ _ ≫ (α_ A Z _).hom ≫
      A ◁ (CategoryTheory.ihom.ev Z).app N.X ≫ act N.X := by
  rw [homAct, uncurry_curry]

/-- `[Z, N]` as an `A`-module through `N`. -/
@[implicit_reducible]
def homModObj (Z : C) (N : Mod C A) : ModObj A ((CategoryTheory.ihom Z).obj N.X) :=
  .mk' A (homAct A Z N)
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_homAct, uncurry_eq,
        associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
        BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
        associator_naturality_left_assoc, ← whisker_exchange_assoc]
      erw [one_act]
      simp)
    (by
      apply uncurry_injective
      rw [uncurry_natural_left, uncurry_homAct, uncurry_natural_left, uncurry_natural_left,
        uncurry_homAct, associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
        BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
        associator_naturality_left_assoc, ← whisker_exchange_assoc]
      erw [mul_act]
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
        associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
        ← uncurry_eq, uncurry_homAct, BraidedCategory.braiding_tensor_right_hom]
      simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
      monoidal)

variable (A) in
/-- `[Z, N]` as an `A`-module through `N`. -/
def homMod (Z : C) (N : Mod C A) : Mod C A :=
  letI := homModObj Z N
  ⟨(CategoryTheory.ihom Z).obj N.X⟩

lemma act_homMod (Z : C) (N : Mod C A) : act (homMod A Z N).X = homAct A Z N := rfl


/-- Post-composition with a morphism of modules is linear. -/
def homModMap (Z : C) {N N' : Mod C A} (f : N ⟶ N') : homMod A Z N ⟶ homMod A Z N' :=
  homMk ((CategoryTheory.ihom Z).map f.hom) (by
    change homAct A Z N ≫ (CategoryTheory.ihom Z).map f.hom =
      A ◁ (CategoryTheory.ihom Z).map f.hom ≫ homAct A Z N'
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_homAct, uncurry_natural_left, uncurry_homAct,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
    erw [ihom.ev_naturality]
    simp only [Category.assoc, act_hom, MonoidalCategory.whiskerLeft_comp_assoc])

/-- Pre-composition is linear. -/
def homModPre {Z Z' : C} (g : Z ⟶ Z') (N : Mod C A) : homMod A Z' N ⟶ homMod A Z N :=
  homMk ((pre g).app N.X) (by
    change homAct A Z' N ≫ (pre g).app N.X = A ◁ (pre g).app N.X ≫ homAct A Z N
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_homAct, uncurry_natural_left, uncurry_homAct,
      associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← uncurry_eq, uncurry_pre, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left,
      comp_whiskerRight_assoc, associator_naturality_middle_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc])

section Comm

variable [IsCommMonObj A]

omit [MonoidalClosed C] in
/-- The actions of `A` on a module commute: `a · (a' · n) = a' · (a · n)`. -/
lemma whiskerLeft_act_comp_act (N : Mod C A) :
    A ◁ act N.X ≫ act N.X =
      (α_ A A N.X).inv ≫ (β_ A A).hom ▷ N.X ≫ (α_ A A N.X).hom ≫ A ◁ act N.X ≫ act N.X := by
  rw [← cancel_epi (α_ A A N.X).hom, ← mul_act, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]

omit [MonoidalClosed C] in
lemma whiskerLeft_whiskerLeft_comp_act_comp_act {X : C} (N : Mod C A) (g : X ⟶ N.X) :
    A ◁ A ◁ g ≫ A ◁ act N.X ≫ act N.X =
      (α_ A A X).inv ≫ (β_ A A).hom ▷ X ≫ (α_ A A X).hom ≫ A ◁ A ◁ g ≫ A ◁ act N.X ≫
        act N.X := by
  conv_lhs => rw [whiskerLeft_act_comp_act, associator_inv_naturality_right_assoc,
    whisker_exchange_assoc, associator_naturality_right_assoc]

variable (A) in
/-- The map `[M, N] ⟶ [A ⊗ M, N]`, `f ↦ (a ⊗ m ↦ a · f(m))`. -/
def homModB (M : Mod C A) (N : Mod C A) : homMod A M.X N ⟶ homMod A (A ⊗ M.X) N :=
  homMk (curry ((α_ A M.X ((CategoryTheory.ihom M.X).obj N.X)).hom ≫
      A ◁ (CategoryTheory.ihom.ev M.X).app N.X ≫ act N.X)) (by
    change homAct A M.X N ≫ curry ((α_ A M.X ((CategoryTheory.ihom M.X).obj N.X)).hom ≫
        A ◁ (CategoryTheory.ihom.ev M.X).app N.X ≫ act N.X) =
      A ◁ curry ((α_ A M.X ((CategoryTheory.ihom M.X).obj N.X)).hom ≫
        A ◁ (CategoryTheory.ihom.ev M.X).app N.X ≫ act N.X) ≫ homAct A (A ⊗ M.X) N
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_homAct,
      associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← uncurry_eq, uncurry_homAct, associator_inv_naturality_right_assoc,
      whisker_exchange_assoc, associator_naturality_right_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ← uncurry_eq, uncurry_curry]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    conv_lhs => rw [whiskerLeft_whiskerLeft_comp_act_comp_act]
    rw [BraidedCategory.braiding_tensor_left_hom]
    simp only [comp_whiskerRight, Category.assoc]
    monoidal)

end Comm

section Adj

variable [IsCommMonObj A]

omit [IsCommMonObj A] in
/-- A morphism `P ⊗ M ⟶ N` is linear in `P` iff its adjoint `P ⟶ [M, N]` is linear. -/
lemma tensorRight_linear_iff (P N : Mod C A) (Z : C) (u : P.X ⊗ Z ⟶ N.X) :
    (α_ A P.X Z).inv ≫ act P.X ▷ Z ≫ u = A ◁ u ≫ act N.X ↔
      act P.X ≫ curry ((β_ Z P.X).hom ≫ u) =
        A ◁ curry ((β_ Z P.X).hom ≫ u) ≫ homAct A Z N := by
  rw [← uncurry_injective.eq_iff, uncurry_natural_left, uncurry_curry, uncurry_natural_left,
    uncurry_homAct, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← uncurry_eq, uncurry_curry, BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]
  exact (cancel_epi ((α_ Z A P.X).inv ≫ (β_ Z A).hom ▷ P.X ≫ (α_ A Z P.X).hom ≫
    A ◁ (β_ Z P.X).hom)).symm.trans (by simp only [Category.assoc])

omit [MonoidalClosed C] [IsCommMonObj A] in
@[reassoc]
lemma braiding_tensor_left_comp_braiding_whiskerRight (X Y Z : C) :
    (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv ≫ (β_ Z X).hom ▷ Y =
      (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).hom ≫ (α_ X Z Y).inv := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight]
  rw [SymmetricCategory.symmetry, id_whiskerRight, Category.comp_id]

omit [IsCommMonObj A] in
/-- For a morphism `u : P ⊗ M ⟶ N` linear in `P`, `u` coequalizes the two actions of `A` on
`P ⊗ M` iff its adjoint `P ⟶ [M, N]` takes values in the linear maps. -/
lemma coequalizes_iff (P M N : Mod C A) (u : P.X ⊗ M.X ⟶ N.X)
    (hu : (α_ A P.X M.X).inv ≫ act P.X ▷ M.X ≫ u = A ◁ u ≫ act N.X) :
    P.X ◁ act M.X ≫ u = (α_ P.X A M.X).inv ≫ rightAct P ▷ M.X ≫ u ↔
      curry ((β_ M.X P.X).hom ≫ u) ≫ (pre (act M.X)).app N.X =
        curry ((β_ M.X P.X).hom ≫ u) ≫ curry ((α_ A M.X ((CategoryTheory.ihom M.X).obj N.X)).hom ≫
          A ◁ (CategoryTheory.ihom.ev M.X).app N.X ≫ act N.X) := by
  rw [← uncurry_injective.eq_iff, uncurry_pre_app, uncurry_curry, uncurry_natural_left,
    uncurry_curry, associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← uncurry_eq, uncurry_curry, MonoidalCategory.whiskerLeft_comp_assoc, ← hu,
    BraidedCategory.braiding_naturality_left_assoc]
  rw [← braiding_tensor_left_comp_braiding_whiskerRight_assoc]
  simp only [Category.assoc, rightAct, comp_whiskerRight]
  exact (cancel_epi (β_ (A ⊗ M.X) P.X).hom).symm

omit [IsCommMonObj A] in
lemma homModMap_comp_homModPre {Z Z' : C} (g : Z ⟶ Z') {N N' : Mod C A} (f : N ⟶ N') :
    homModMap Z' f ≫ homModPre g N' = homModPre g N ≫ homModMap Z f :=
  Mod.hom_ext _ _ ((pre g).naturality f.hom)

omit [IsCommMonObj A] in
lemma homModMap_id (Z : C) (N : Mod C A) : homModMap Z (𝟙 N) = 𝟙 _ :=
  Mod.hom_ext _ _ ((CategoryTheory.ihom Z).map_id _)

omit [IsCommMonObj A] in
lemma homModMap_comp (Z : C) {N N' N'' : Mod C A} (f : N ⟶ N') (g : N' ⟶ N'') :
    homModMap Z (f ≫ g) = homModMap Z f ≫ homModMap Z g :=
  Mod.hom_ext _ _ ((CategoryTheory.ihom Z).map_comp _ _)

lemma homModMap_comp_homModB (M : Mod C A) {N N' : Mod C A} (f : N ⟶ N') :
    homModMap M.X f ≫ homModB A M N' = homModB A M N ≫ homModMap (A ⊗ M.X) f := by
  refine Mod.hom_ext _ _ ?_
  change (CategoryTheory.ihom M.X).map f.hom ≫ curry _ = curry _ ≫
    (CategoryTheory.ihom (A ⊗ M.X)).map f.hom
  rw [← curry_natural_left, ← curry_natural_right]
  congr 1
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [ihom.ev_naturality]
  simp

variable [HasLimitsOfShape WalkingParallelPair C]

variable (A) in
/-- The internal hom `Hom_A(M, N)` of modules over a commutative monoid: the equalizer of
`[M, N] ⇉ [A ⊗ M, N]`, `f ↦ f ∘ act_M` and `f ↦ act_N ∘ (A ⊗ f)`. -/
noncomputable def ihom' (M : Mod C A) : Mod C A ⥤ Mod C A where
  obj N := equalizer (homModPre (act M.X) N) (homModB A M N)
  map f := equalizer.lift (equalizer.ι _ _ ≫ homModMap M.X f) (by
    rw [Category.assoc, Category.assoc, homModMap_comp_homModPre, homModMap_comp_homModB,
      equalizer.condition_assoc])
  map_id _ := equalizer.hom_ext (by
    rw [equalizer.lift_ι, homModMap_id, Category.comp_id, Category.id_comp])
  map_comp _ _ := equalizer.hom_ext (by
    rw [equalizer.lift_ι, Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      homModMap_comp, Category.assoc])

variable [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]

/-- The adjoint `P ⟶ Hom_A(M, N)` of a morphism `P ⊗ M ⟶ N` coequalizing the two actions. -/
noncomputable def ihomLift {P M N : Mod C A} (u : (tensorRight A M.X).obj P ⟶ N)
    (hu : (tensorRightMap A (act M.X)).app P ≫ u = (tensorRightRightAct A M.X).app P ≫ u) :
    P ⟶ (ihom' A M).obj N :=
  have hlin : (α_ A P.X M.X).inv ≫ act P.X ▷ M.X ≫ u.hom = A ◁ u.hom ≫ act N.X := by
    exact (Category.assoc _ _ _).symm.trans (act_hom u)
  equalizer.lift (homMk (M := P) (N := homMod A M.X N) (curry ((β_ M.X P.X).hom ≫ u.hom))
    ((tensorRight_linear_iff P N M.X u.hom).1 hlin)) (Mod.hom_ext _ _ (by
      have h2 : P.X ◁ act M.X ≫ u.hom = (α_ P.X A M.X).inv ≫ rightAct P ▷ M.X ≫ u.hom := by
        have := congrArg Mod.Hom.hom hu
        simp only [Mod.comp_hom', tensorRightMap_app_hom, tensorRightRightAct_app_hom,
          Category.assoc] at this
        simpa only [rightAct, comp_whiskerRight, Category.assoc] using this
      exact (coequalizes_iff P M N u.hom hlin).1 h2))

/-- The morphism `P ⊗ M ⟶ N` adjoint to `P ⟶ Hom_A(M, N)`. -/
noncomputable def ihomDesc {P M N : Mod C A} (v : P ⟶ (ihom' A M).obj N) :
    (tensorRight A M.X).obj P ⟶ N :=
  homMk (M := (tensorRight A M.X).obj P) ((β_ M.X P.X).inv ≫ uncurry (v ≫ equalizer.ι _ _).hom)
    (by
      refine (Category.assoc _ _ _).trans ((tensorRight_linear_iff P N M.X _).2 ?_)
      rw [Iso.hom_inv_id_assoc, curry_uncurry]
      exact act_hom (v ≫ equalizer.ι _ _))

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma ihomDesc_hom {P M N : Mod C A} (v : P ⟶ (ihom' A M).obj N) :
    (ihomDesc v).hom = (β_ M.X P.X).inv ≫ uncurry (v ≫ equalizer.ι _ _).hom := rfl

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma ihomDesc_coequalizes {P M N : Mod C A} (v : P ⟶ (ihom' A M).obj N) :
    (tensorRightMap A (act M.X)).app P ≫ ihomDesc v =
      (tensorRightRightAct A M.X).app P ≫ ihomDesc v := by
  have hlin : (α_ A P.X M.X).inv ≫ act P.X ▷ M.X ≫ (ihomDesc v).hom =
      A ◁ (ihomDesc v).hom ≫ act N.X :=
    (Category.assoc _ _ _).symm.trans (act_hom (ihomDesc v))
  have h := (coequalizes_iff P M N _ hlin).2 (by
    rw [ihomDesc_hom, Iso.hom_inv_id_assoc, curry_uncurry]
    exact congrArg Mod.Hom.hom ((Category.assoc _ _ _).trans
      ((congrArg (v ≫ ·) (equalizer.condition _ _)).trans (Category.assoc _ _ _).symm)))
  refine Mod.hom_ext _ _ ?_
  simp only [Mod.comp_hom', tensorRightMap_app_hom, tensorRightRightAct_app_hom,
    Category.assoc]
  simpa only [rightAct, comp_whiskerRight, Category.assoc] using h

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma ihomLift_ι {P M N : Mod C A} (u : (tensorRight A M.X).obj P ⟶ N)
    (hu : (tensorRightMap A (act M.X)).app P ≫ u = (tensorRightRightAct A M.X).app P ≫ u) :
    (ihomLift u hu ≫ equalizer.ι _ _).hom = curry ((β_ M.X P.X).hom ≫ u.hom) := by
  rw [ihomLift, equalizer.lift_ι]
  rfl

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
@[reassoc]
lemma ihomLift_hom_comp_ι {P M N : Mod C A} (u : (tensorRight A M.X).obj P ⟶ N)
    (hu : (tensorRightMap A (act M.X)).app P ≫ u = (tensorRightRightAct A M.X).app P ≫ u) :
    (ihomLift u hu).hom ≫ (equalizer.ι (homModPre (act M.X) N) (homModB A M N)).hom =
      curry ((β_ M.X P.X).hom ≫ u.hom) :=
  ihomLift_ι u hu

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma ihom'_map_ι (M : Mod C A) {N N' : Mod C A} (f : N ⟶ N') :
    (ihom' A M).map f ≫ equalizer.ι _ _ = equalizer.ι _ _ ≫ homModMap M.X f :=
  equalizer.lift_ι _ _

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma ihomDesc_ihomLift {P M N : Mod C A} (u : (tensorRight A M.X).obj P ⟶ N)
    (hu : (tensorRightMap A (act M.X)).app P ≫ u = (tensorRightRightAct A M.X).app P ≫ u) :
    ihomDesc (ihomLift u hu) = u :=
  Mod.hom_ext _ _ (by rw [ihomDesc_hom, ihomLift_ι, uncurry_curry, Iso.inv_hom_id_assoc])

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma ihomLift_ihomDesc {P M N : Mod C A} (v : P ⟶ (ihom' A M).obj N) :
    ihomLift (ihomDesc v) (ihomDesc_coequalizes v) = v :=
  equalizer.hom_ext (Mod.hom_ext _ _ (by
    rw [ihomLift_ι, ihomDesc_hom, Iso.hom_inv_id_assoc, curry_uncurry]))

omit [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)] in
lemma ihomDesc_comp {P P' M N : Mod C A} (g : P' ⟶ P) (v : P ⟶ (ihom' A M).obj N) :
    ihomDesc (g ≫ v) = (tensorRight A M.X).map g ≫ ihomDesc v :=
  Mod.hom_ext _ _ (by
    simp only [ihomDesc_hom, Mod.comp_hom', tensorRight_map_hom, Category.assoc,
      uncurry_natural_left]
    rw [BraidedCategory.braiding_inv_naturality_left_assoc])

/-- The cocone on the parallel pair defining `P ⊗_A M` given by a morphism `P ⟶ Hom_A(M, N)`. -/
noncomputable def ihomCocone {P M N : Mod C A} (v : P ⟶ (ihom' A M).obj N) :
    Cocone ((tensorLeftDiagram A M).flip.obj P) where
  pt := N
  ι :=
    { app j := match j with
        | .zero => (tensorRightMap A (act M.X)).app P ≫ ihomDesc v
        | .one => ihomDesc v
      naturality := by
        rintro _ _ (_ | _ | _)
        · exact (Category.comp_id ((tensorRightMap A (act M.X)).app P ≫ ihomDesc v)).symm
        · exact (ihomDesc_coequalizes v).symm.trans
            (Category.comp_id ((tensorRightMap A (act M.X)).app P ≫ ihomDesc v)).symm
        · simp }

variable (A) in
/-- **The tensor–hom adjunction for modules over a commutative monoid**. -/
noncomputable def ihom'Adjunction (M : Mod C A) : tensorLeft M ⊣ ihom' A M :=
  Adjunction.mkOfHomEquiv
    { homEquiv P N :=
        { toFun φ := ihomLift (colimit.ι ((tensorLeftDiagram A M).flip.obj P)
              WalkingParallelPair.one ≫ φ) (by
            exact (colimit.w_assoc _ WalkingParallelPairHom.left φ).trans
              (colimit.w_assoc _ WalkingParallelPairHom.right φ).symm)
          invFun v := colimit.desc _ (ihomCocone v)
          left_inv φ := by
            refine colimit.hom_ext fun j ↦ ?_
            cases j
            · rw [colimit.ι_desc]
              change (tensorRightMap A (act M.X)).app P ≫ ihomDesc (ihomLift _ _) = _
              rw [ihomDesc_ihomLift]
              exact colimit.w_assoc _ WalkingParallelPairHom.left φ
            · rw [colimit.ι_desc]
              exact ihomDesc_ihomLift _ _
          right_inv v := by
            change ihomLift _ _ = v
            simp only [colimit.ι_desc]
            exact ihomLift_ihomDesc v }
      homEquiv_naturality_left_symm g v := by
        refine colimit.hom_ext fun j ↦ ?_
        change colimit.ι _ j ≫ colimit.desc _ (ihomCocone (g ≫ v)) =
          colimit.ι _ j ≫ colim.map ((tensorLeftDiagram A M).flip.map g) ≫
            colimit.desc _ (ihomCocone v)
        rw [colimit.ι_desc, colimit.ι_map_assoc, colimit.ι_desc]
        cases j
        · change (tensorRightMap A (act M.X)).app _ ≫ ihomDesc (g ≫ v) =
            (tensorRight A (A ⊗ M.X)).map g ≫ (tensorRightMap A (act M.X)).app _ ≫ ihomDesc v
          rw [ihomDesc_comp, ← NatTrans.naturality_assoc]
        · exact ihomDesc_comp g v
      homEquiv_naturality_right φ f := by
        refine equalizer.hom_ext (Mod.hom_ext _ _ ?_)
        simp only [Equiv.coe_fn_mk, Category.assoc, ihom'_map_ι, Mod.comp_hom',
          ihomLift_hom_comp_ι]
        rw [ihomLift_hom_comp_ι_assoc]
        change _ = _ ≫ (CategoryTheory.ihom M.X).map f.hom
        rw [← curry_natural_right]
        simp only [Category.assoc, Mod.comp_hom'] }

end Adj

end CategoryTheory.Mod

namespace CategoryTheory.Mod

section Functor

open scoped Obj

open Functor.LaxMonoidal

variable {C D : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [Category D] [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {A : C} [MonObj A] {B : D} [MonObj B]
  (F : C ⥤ D) [F.LaxBraided] (ρ : B ⟶ F.obj A) [IsMonHom ρ]

/-- The comparison `F [Z, N] ⟶ [F Z, F N]` is linear. -/
def mapHomModHom (Z : C) (N : Mod C A) :
    (comap ρ).obj ((F.mapMod A).obj (homMod A Z N)) ⟶
      homMod B (F.obj Z) ((comap ρ).obj ((F.mapMod A).obj N)) :=
  homMk ((ihomComparison F Z).app N.X) (by
    change (ρ ▷ _ ≫ Functor.LaxMonoidal.μ F A ((CategoryTheory.ihom Z).obj N.X) ≫
        F.map (homAct A Z N)) ≫
        (ihomComparison F Z).app N.X =
      B ◁ (ihomComparison F Z).app N.X ≫
        homAct B (F.obj Z) ((comap ρ).obj ((F.mapMod A).obj N))
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_eq, ihomComparison_ev, uncurry_natural_left,
      uncurry_homAct]
    change _ = F.obj Z ◁ B ◁ (ihomComparison F Z).app N.X ≫
      (α_ (F.obj Z) B ((CategoryTheory.ihom (F.obj Z)).obj (F.obj N.X))).inv ≫
      (β_ (F.obj Z) B).hom ▷ _ ≫ (α_ B (F.obj Z) _).hom ≫
      B ◁ (CategoryTheory.ihom.ev (F.obj Z)).app (F.obj N.X) ≫
      ρ ▷ _ ≫ Functor.LaxMonoidal.μ F A N.X ≫ F.map (act N.X)
    erw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
      associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ihomComparison_ev]
    dsimp only [Functor.id_obj, Functor.comp_obj]
    rw [whisker_exchange_assoc, ← associator_naturality_left_assoc,
      ← comp_whiskerRight_assoc, ← BraidedCategory.braiding_naturality_right,
      comp_whiskerRight_assoc, ← associator_inv_naturality_middle_assoc]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    congr 1
    rw [μ_natural_right_assoc, ← F.map_comp, ← uncurry_eq, uncurry_homAct]
    simp only [Functor.map_comp]
    rw [μ_natural_right_assoc, associativity_inv_assoc, ← μ_natural_left_assoc,
      ← comp_whiskerRight_assoc, Functor.LaxBraided.braided, comp_whiskerRight_assoc,
      associativity_assoc])

/-- The comparison maps of internal homs are natural in the first variable. -/
@[reassoc]
lemma map_pre_app_comp_ihomComparison {Z Z' : C} (g : Z ⟶ Z') (Y : C) :
    F.map ((pre g).app Y) ≫ (ihomComparison F Z).app Y =
      (ihomComparison F Z').app Y ≫ (pre (F.map g)).app (F.obj Y) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_eq]
  erw [ihomComparison_ev]
  rw [μ_natural_right_assoc, ← F.map_comp, ← uncurry_eq, uncurry_pre, uncurry_pre_app,
    uncurry_eq]
  erw [ihomComparison_ev]
  rw [μ_natural_left_assoc, F.map_comp]

lemma mapHomModHom_hom (Z : C) (N : Mod C A) :
    (mapHomModHom F ρ Z N).hom = (ihomComparison F Z).app N.X := rfl

/-- Compatibility of the comparison with `f ↦ f ∘ act_M`. -/
lemma mapHomModHom_homModPre (M N : Mod C A) :
    (F.mapMod A ⋙ comap ρ).map (homModPre (act M.X) N) ≫ mapHomModHom F ρ (A ⊗ M.X) N ≫
        homModPre (ρ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X) _ =
      mapHomModHom F ρ M.X N ≫ homModPre (act ((F.mapMod A ⋙ comap ρ).obj M).X) _ := by
  refine Mod.hom_ext _ _ ?_
  change F.map ((pre (act M.X)).app N.X) ≫ (ihomComparison F (A ⊗ M.X)).app N.X ≫
      (pre (ρ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X)).app (F.obj N.X) =
    (ihomComparison F M.X).app N.X ≫
      (pre (ρ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X ≫ F.map (act M.X))).app (F.obj N.X)
  rw [map_pre_app_comp_ihomComparison_assoc, ← NatTrans.comp_app, ← pre_map, Category.assoc]

/-- Compatibility of the comparison with `f ↦ act_N ∘ (A ⊗ f)`. -/
lemma mapHomModHom_homModB [IsCommMonObj A] [IsCommMonObj B] (M N : Mod C A) :
    (F.mapMod A ⋙ comap ρ).map (homModB A M N) ≫ mapHomModHom F ρ (A ⊗ M.X) N ≫
        homModPre (ρ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X) _ =
      mapHomModHom F ρ M.X N ≫ homModB B ((F.mapMod A ⋙ comap ρ).obj M) _ := by
  refine Mod.hom_ext _ _ ?_
  change F.map (curry ((α_ A M.X ((CategoryTheory.ihom M.X).obj N.X)).hom ≫
        A ◁ (CategoryTheory.ihom.ev M.X).app N.X ≫ act N.X)) ≫
      (ihomComparison F (A ⊗ M.X)).app N.X ≫
      (pre (ρ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X)).app (F.obj N.X) =
    (ihomComparison F M.X).app N.X ≫
      curry ((α_ B (F.obj M.X) ((CategoryTheory.ihom (F.obj M.X)).obj (F.obj N.X))).hom ≫
        B ◁ (CategoryTheory.ihom.ev (F.obj M.X)).app (F.obj N.X) ≫
          ρ ▷ F.obj N.X ≫ Functor.LaxMonoidal.μ F A N.X ≫ F.map (act N.X))
  apply uncurry_injective
  rw [← Category.assoc, uncurry_pre_app, uncurry_natural_left, uncurry_eq]
  erw [ihomComparison_ev]
  rw [μ_natural_right_assoc, ← F.map_comp, ← uncurry_eq, uncurry_curry, uncurry_natural_left,
    uncurry_curry]
  erw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ihomComparison_ev]
  erw [whisker_exchange_assoc]
  rw [← associator_naturality_left_assoc]
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  erw [μ_natural_right_assoc]
  rw [associativity_assoc]

lemma mapHomModHom_naturality (Z : C) {N N' : Mod C A} (f : N ⟶ N') :
    (F.mapMod A ⋙ comap ρ).map (homModMap Z f) ≫ mapHomModHom F ρ Z N' =
      mapHomModHom F ρ Z N ≫ homModMap (F.obj Z) ((F.mapMod A ⋙ comap ρ).map f) :=
  Mod.hom_ext _ _ ((ihomComparison F Z).naturality f.hom)

section Ihom

variable [IsCommMonObj A] [IsCommMonObj B] [HasLimitsOfShape WalkingParallelPair C]
  [HasLimitsOfShape WalkingParallelPair D]

/-- The comparison `F Hom_A(M, N) ⟶ Hom_B(F M, F N)` of internal homs of modules. -/
noncomputable def mapIhom'Hom (M N : Mod C A) :
    (F.mapMod A ⋙ comap ρ).obj ((ihom' A M).obj N) ⟶
      (ihom' B ((F.mapMod A ⋙ comap ρ).obj M)).obj ((F.mapMod A ⋙ comap ρ).obj N) :=
  equalizer.lift ((F.mapMod A ⋙ comap ρ).map (equalizer.ι _ _) ≫ mapHomModHom F ρ M.X N) (by
    rw [Category.assoc, Category.assoc]
    erw [← mapHomModHom_homModPre, ← mapHomModHom_homModB]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, equalizer.condition])

@[reassoc (attr := simp)]
lemma mapIhom'Hom_ι (M N : Mod C A) :
    mapIhom'Hom F ρ M N ≫ equalizer.ι _ _ =
      (F.mapMod A ⋙ comap ρ).map (equalizer.ι _ _) ≫ mapHomModHom F ρ M.X N :=
  equalizer.lift_ι _ _

lemma mapIhom'Hom_naturality (M : Mod C A) {N N' : Mod C A} (f : N ⟶ N') :
    (F.mapMod A ⋙ comap ρ).map ((ihom' A M).map f) ≫ mapIhom'Hom F ρ M N' =
      mapIhom'Hom F ρ M N ≫ (ihom' B _).map ((F.mapMod A ⋙ comap ρ).map f) := by
  refine equalizer.hom_ext ?_
  rw [Category.assoc]
  erw [mapIhom'Hom_ι]
  rw [← Functor.map_comp_assoc, ihom'_map_ι, Functor.map_comp_assoc, mapHomModHom_naturality,
    Category.assoc]
  erw [ihom'_map_ι, mapIhom'Hom_ι_assoc]
  rfl

/-- If `F` commutes with internal homs and equalizers, the comparison of internal homs of modules
is an isomorphism. -/
lemma isIso_mapIhom'Hom (M N : Mod C A) [IsIso ρ]
    [∀ Z : C, IsIso (ihomComparison F Z)]
    [IsIso (Functor.LaxMonoidal.μ F A M.X)]
    [PreservesLimit (parallelPair (homModPre (act M.X) N) (homModB A M N))
      (F.mapMod A ⋙ comap ρ)] :
    IsIso (mapIhom'Hom F ρ M N) := by
  let Φ := F.mapMod A ⋙ comap ρ
  let a := homModPre (act (A := A) M.X) N
  let b := homModB A M N
  let a' := homModPre (act (A := B) (Φ.obj M).X) (Φ.obj N)
  let b' := homModB B (Φ.obj M) (Φ.obj N)
  let p := ρ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X
  let u := mapHomModHom F ρ M.X N
  let v := mapHomModHom F ρ (A ⊗ M.X) N ≫ homModPre p (Φ.obj N)
  have hiso {X Y : Mod D B} (f : X ⟶ Y) (hf : IsIso f.hom) : IsIso f :=
    have : IsIso ((forget B).map f) := hf
    isIso_of_reflects_iso f (forget B)
  have hu : IsIso u := hiso _ (inferInstanceAs (IsIso ((ihomComparison F M.X).app N.X)))
  have hv : IsIso v := by
    have : IsIso (mapHomModHom F ρ (A ⊗ M.X) N) :=
      hiso _ (inferInstanceAs (IsIso ((ihomComparison F (A ⊗ M.X)).app N.X)))
    have : IsIso (homModPre p (Φ.obj N)) := hiso _ (inferInstanceAs (IsIso ((pre p).app _)))
    infer_instance
  have ha : Φ.map a ≫ v = u ≫ a' := mapHomModHom_homModPre F ρ M N
  have hb : Φ.map b ≫ v = u ≫ b' := mapHomModHom_homModB F ρ M N
  have hl := isLimitForkMapOfIsLimit Φ (equalizer.condition a b) (equalizerIsEqualizer a b)
  refine ⟨Fork.IsLimit.lift hl (equalizer.ι a' b' ≫ inv u) ?_, ?_, ?_⟩
  · rw [← cancel_mono v, Category.assoc, Category.assoc, Category.assoc, Category.assoc, ha, hb,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc, equalizer.condition]
  · refine Fork.IsLimit.hom_ext hl ?_
    erw [Category.assoc, Fork.IsLimit.lift_ι, mapIhom'Hom_ι_assoc, Category.id_comp]
    simp only [u, IsIso.hom_inv_id, Category.comp_id]
    rfl
  · refine equalizer.hom_ext ?_
    erw [Category.assoc, mapIhom'Hom_ι, Category.id_comp]
    erw [Fork.IsLimit.lift_ι_assoc]
    change (equalizer.ι a' b' ≫ inv u) ≫ u = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end Ihom

end Functor

end CategoryTheory.Mod

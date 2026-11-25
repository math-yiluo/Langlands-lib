/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom

/-!
# Morphisms into internal homs of modules

Let `A` be a commutative monoid in a braided monoidal Grothendieck abelian category `C`, and `D`,
`N` modules over `A`. A morphism `f : X ⟶ Hom_A(D, N)` from an arbitrary object `X` of `C` is
determined by its uncurried form `f ▷ D ≫ ev : X ⊗ D ⟶ N`
(`CategoryTheory.Mod.hom_ext_of_evaluation`), and every morphism `q : X ⊗ D ⟶ N` which is
`A`-linear in `D` is the uncurried form of a morphism `X ⟶ Hom_A(D, N)`
(`CategoryTheory.Mod.curry`). Both use the free module `A ⊗ X` on `X`
(`CategoryTheory.Mod.free`, `CategoryTheory.Mod.freeDesc`).

As an application we construct the morphism `M ⊗ N ⟶ Hom_A(Hom_A(M, A), N)`,
`m ⊗ n ↦ (φ ↦ φ(m) n)` (`CategoryTheory.Mod.toIhomDual`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

/-- The evaluation `Hom_A(M, N) ⊗ M ⟶ N` is `A`-linear in the first variable. -/
@[reassoc]
lemma act_whiskerRight_evaluation (M N : Mod C A) :
    act ((ihom M).obj N).X ▷ M.X ≫ evaluation M N =
      (α_ A _ M.X).hom ≫ A ◁ evaluation M N ≫ act N.X := by
  have h₁ : ((α_ A _ M.X).inv ≫ act ((ihom M).obj N).X ▷ M.X) ≫ tensorπ ((ihom M).obj N) M =
      A ◁ tensorπ ((ihom M).obj N) M ≫ act ((tensorLeft M).obj ((ihom M).obj N)).X :=
    act_hom (tensorLeftπ M ((ihom M).obj N))
  have h₂ : act ((tensorLeft M).obj ((ihom M).obj N)).X ≫
      ((ihomAdjunction M).counit.app N).hom =
      A ◁ ((ihomAdjunction M).counit.app N).hom ≫ act N.X :=
    act_hom _
  rw [evaluation, ← Iso.hom_inv_id_assoc (α_ A _ M.X) (act _ ▷ M.X ≫ _), ← Category.assoc
    (α_ A _ M.X).inv, ← Category.assoc ((α_ A _ M.X).inv ≫ _), h₁, Category.assoc, h₂,
    MonoidalCategory.whiskerLeft_comp_assoc]

/-- The evaluation `Hom_A(M, N) ⊗ M ⟶ N` is `A`-balanced. -/
@[reassoc]
lemma whiskerLeft_act_evaluation (M N : Mod C A) :
    ((ihom M).obj N).X ◁ act M.X ≫ evaluation M N =
      (α_ _ A M.X).inv ≫ rightAct ((ihom M).obj N) ▷ M.X ≫ evaluation M N := by
  have h := colimit.w ((tensorLeftDiagram A M).flip.obj ((ihom M).obj N))
    WalkingParallelPairHom.left
  have h' := colimit.w ((tensorLeftDiagram A M).flip.obj ((ihom M).obj N))
    WalkingParallelPairHom.right
  have e : ((ihom M).obj N).X ◁ act M.X ≫ tensorπ ((ihom M).obj N) M =
      ((α_ _ A M.X).inv ≫ rightAct ((ihom M).obj N) ▷ M.X) ≫ tensorπ ((ihom M).obj N) M :=
    congrArg Mod.Hom.hom (h.trans h'.symm)
  simp only [evaluation]
  rw [reassoc_of% e]

/-- **Morphisms into internal homs are determined by their uncurried form.** -/
lemma hom_ext_of_evaluation {X : C} {D N : Mod C A} {f g : X ⟶ ((ihom D).obj N).X}
    (h : f ▷ D.X ≫ evaluation D N = g ▷ D.X ≫ evaluation D N) : f = g := by
  suffices freeDesc A f = freeDesc A g by
    rw [← unit_freeDesc A f, ← unit_freeDesc A g, this]
  apply ihom_hom_ext
  apply tensorLeft_hom_ext
  ext1
  simp only [Mod.comp_hom']
  have key (φ : X ⟶ ((ihom D).obj N).X) : (tensorLeftπ D ((free A).obj X)).hom ≫
      ((tensorLeft D).map (freeDesc A φ)).hom ≫ ((ihomAdjunction D).counit.app N).hom =
      (α_ A X D.X).hom ≫ A ◁ (φ ▷ D.X ≫ evaluation D N) ≫ act N.X := by
    have := tensorπ_map D (freeDesc A φ)
    change tensorπ _ D ≫ _ = _ ▷ D.X ≫ tensorπ _ D at this
    change tensorπ _ D ≫ _ ≫ _ = _
    rw [reassoc_of% this, freeDesc_hom, comp_whiskerRight, Category.assoc,
      ← evaluation, act_whiskerRight_evaluation, associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [key, key, h]

/-- `q : X ⊗ D ⟶ N` is `A`-linear in `D`. -/
def IsLinearRight {X : C} {D N : Mod C A} (q : X ⊗ D.X ⟶ N.X) : Prop :=
  X ◁ act D.X ≫ q =
    (α_ X A D.X).inv ≫ (β_ X A).hom ▷ D.X ≫ (α_ A X D.X).hom ≫ A ◁ q ≫ act N.X

variable {X : C} {D N : Mod C A} (q : X ⊗ D.X ⟶ N.X)

/-- The morphism `(A ⊗ X) ⊗ D ⟶ N`, `(a ⊗ x) ⊗ d ↦ a • q (x ⊗ d)`, of `A`-modules. -/
noncomputable def curryAux : (tensorRight A D.X).obj ((free A).obj X) ⟶ N :=
  homMk ((α_ A X D.X).hom ≫ A ◁ q ≫ act N.X) (by
    change ((α_ A (A ⊗ X) D.X).inv ≫ ((α_ A A X).inv ≫ μ[A] ▷ X) ▷ D.X) ≫
        (α_ A X D.X).hom ≫ A ◁ q ≫ act N.X =
      A ◁ ((α_ A X D.X).hom ≫ A ◁ q ≫ act N.X) ≫ act N.X
    simp only [comp_whiskerRight, Category.assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, mul_act,
      associator_naturality_right_assoc]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    monoidal)

omit [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)] in
/-- The morphism `curryAux q` coequalizes the two actions of `A` defining `(A ⊗ X) ⊗_A D`. -/
lemma curryAux_condition (hq : IsLinearRight q) :
    (tensorRightMap A (act D.X)).app ((free A).obj X) ≫ curryAux q =
      (tensorRightRightAct A D.X).app ((free A).obj X) ≫ curryAux q := by
  ext1
  simp only [Mod.comp_hom', tensorRightMap_app_hom, tensorRightRightAct_app_hom, curryAux,
    homMk_hom]
  change (A ⊗ X) ◁ act D.X ≫ (α_ A X D.X).hom ≫ A ◁ q ≫ act N.X =
    ((α_ (A ⊗ X) A D.X).inv ≫ (β_ (A ⊗ X) A).hom ▷ D.X ≫ ((α_ A A X).inv ≫ μ[A] ▷ X) ▷ D.X) ≫
      (α_ A X D.X).hom ≫ A ◁ q ≫ act N.X
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hq,
    BraidedCategory.braiding_tensor_left_hom]
  simp only [comp_whiskerRight, Category.assoc, MonoidalCategory.whiskerLeft_comp,
    hom_inv_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc ((β_ A A).hom ▷ X) (μ ▷ X), ← comp_whiskerRight (β_ A A).hom,
    IsCommMonObj.mul_comm, associator_naturality_left_assoc, ← whisker_exchange_assoc, mul_act]
  monoidal

/-- The morphism `(A ⊗ X) ⊗_A D ⟶ N` induced by `q`. -/
noncomputable def curryTensorLeft (hq : IsLinearRight q) :
    (tensorLeft D).obj ((free A).obj X) ⟶ N :=
  colimit.desc _ ((Cocone.precompose (diagramIsoParallelPair _).hom).obj
    (Cofork.ofπ (curryAux q) (curryAux_condition q hq)))

omit [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)] in
/-- The morphism `(A ⊗ X) ⊗_A D ⟶ N` induced by `q` on the quotient map. -/
lemma tensorπ_curryTensorLeft (hq : IsLinearRight q) :
    tensorπ ((free A).obj X) D ≫ (curryTensorLeft q hq).hom =
      (α_ A X D.X).hom ≫ A ◁ q ≫ act N.X := by
  change ((tensorLeftπ D ((free A).obj X)) ≫ curryTensorLeft q hq).hom = _
  rw [curryTensorLeft, colimit.ι_desc]
  simp [curryAux]

/-- **Currying.** The morphism `X ⟶ Hom_A(D, N)` whose uncurried form is a morphism
`q : X ⊗ D ⟶ N` which is `A`-linear in `D`. -/
noncomputable def curry (hq : IsLinearRight q) : X ⟶ ((ihom D).obj N).X :=
  (λ_ X).inv ≫ η[A] ▷ X ≫ ((ihomAdjunction D).homEquiv _ _ (curryTensorLeft q hq)).hom

/-- The uncurried form of `curry q` is `q`. -/
lemma curry_evaluation (hq : IsLinearRight q) : curry q hq ▷ D.X ≫ evaluation D N = q := by
  have h₁ := tensorπ_map D ((ihomAdjunction D).homEquiv _ _ (curryTensorLeft q hq))
  have h₂ : (tensorLeft D).map ((ihomAdjunction D).homEquiv _ _ (curryTensorLeft q hq)) ≫
      (ihomAdjunction D).counit.app N = curryTensorLeft q hq := by
    have := (ihomAdjunction D).homEquiv_counit _ _
      ((ihomAdjunction D).homEquiv _ _ (curryTensorLeft q hq))
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  have h₃ := congrArg Mod.Hom.hom h₂
  rw [Mod.comp_hom'] at h₃
  rw [curry, evaluation, comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    ← reassoc_of% h₁, h₃, tensorπ_curryTensorLeft, associator_naturality_left_assoc,
    ← whisker_exchange_assoc]
  erw [one_act]
  monoidal

end CategoryTheory.Mod

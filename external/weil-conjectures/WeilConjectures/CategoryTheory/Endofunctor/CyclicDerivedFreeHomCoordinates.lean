/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedFreeResolutionCoordinates
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.HomCongr

/-! # Additive Hom coordinates of the free cyclic triangle

Source: Stacks 0149 and 015F and the free/forgetful adjunction.
(blueprint: lem-sf-cyclic-free-hom-coordinates).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w wF

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{wF} (IsoAlgebra F)]

/-- The free adjunction in degree zero, with the specified zero-shift identification.
Source: Stacks 015F (blueprint: lem-sf-cyclic-free-hom-coordinates). -/
def cyclicDerivedFreeHomEquiv (M N : DerivedCategory (IsoAlgebra F)) :
    ((cyclicDerivedFreeFunctor F).obj M ⟶ N) ≃+ CyclicDerivedHom F M N 0 :=
  (cyclicDerivedFreeAdjunction F).homAddEquiv _ N |>.trans
    { (Iso.homCongr (Iso.refl _) ((shiftFunctorZero _ ℤ).symm.app _)) with
      map_add' := fun f g ↦ by simp [Iso.homCongr, Preadditive.add_comp] }

/-- The usual shift equivalence as an adjunction with explicit shift-functor types.
Source: Stacks 0149 (blueprint: lem-sf-cyclic-free-hom-coordinates). -/
def cyclicDerivedFreeShiftAdjunction :
    shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ) ⊣
      shiftFunctor (DerivedCategory (IsoAlgebra F)) (-1 : ℤ) :=
  (shiftEquiv _ (1 : ℤ)).toAdjunction

/-- The free adjunction after moving the source shift to the target.
Source: Stacks 015F (blueprint: lem-sf-cyclic-free-hom-coordinates). -/
def cyclicDerivedFreeShiftedHomEquiv (M N : DerivedCategory (IsoAlgebra F)) :
    (((cyclicDerivedFreeFunctor F).obj M)⟦(1 : ℤ)⟧ ⟶ N) ≃+
      CyclicDerivedHom F M N (-1) :=
  ((cyclicDerivedFreeShiftAdjunction F).homAddEquiv _ N).trans
    (((cyclicDerivedFreeAdjunction F).homAddEquiv _ (N⟦(-1 : ℤ)⟧)).trans
      { (Iso.homCongr (Iso.refl _)
          (((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).app N)) with
        map_add' := fun f g ↦ by simp [Iso.homCongr, Preadditive.add_comp] })

/-- Evaluation of the shifted Hom coordinates without unfolding the shift adjunction.
Source: the two adjunctions, Stacks 015F
(blueprint: lem-sf-cyclic-free-hom-coordinates). -/
theorem cyclicDerivedFreeShiftedHomEquiv_apply
    (M N : DerivedCategory (IsoAlgebra F))
    (f : ((cyclicDerivedFreeFunctor F).obj M)⟦(1 : ℤ)⟧ ⟶ N) :
    cyclicDerivedFreeShiftedHomEquiv F M N f =
      (cyclicDerivedFreeAdjunction F).homEquiv _ (N⟦(-1 : ℤ)⟧)
          ((cyclicDerivedFreeShiftAdjunction F).homEquiv _ N f) ≫
        ((forget F).mapDerivedCategory.commShiftIso (-1 : ℤ)).hom.app N := by
  change 𝟙 _ ≫ _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- The counit induces the actual forgetting map in these coordinates.
Source: adjunction triangle identity, Stacks 015F
(blueprint: lem-sf-cyclic-free-hom-coordinates). -/
theorem cyclicDerivedFreeHomEquiv_counit (M N : DerivedCategory (IsoAlgebra F))
    (f : M ⟶ N) :
    cyclicDerivedFreeHomEquiv F M N ((cyclicDerivedFreeAdjunction F).counit.app M ≫ f) =
      cyclicDerivedForget F M N f := by
  dsimp [cyclicDerivedFreeHomEquiv, Iso.homCongr, cyclicDerivedForget]
  rw [Adjunction.homEquiv_naturality_right,
    ← (cyclicDerivedFreeAdjunction F).homEquiv_symm_id M]
  simp [Preadditive.rightComp]

/-- Naturality of the shifted Hom coordinates in both variables.
Source: naturality of the two adjunctions and the shift comparison, Stacks 015F
(blueprint: lem-sf-cyclic-free-hom-coordinates). -/
theorem cyclicDerivedFreeShiftedHomEquiv_naturality
    (M N M' N' : DerivedCategory (IsoAlgebra F)) (a : M' ⟶ M) (c : N ⟶ N')
    (f : (((cyclicDerivedFreeFunctor F).obj M)⟦(1 : ℤ)⟧) ⟶ N) :
    cyclicDerivedFreeShiftedHomEquiv F M' N'
        (((cyclicDerivedFreeFunctor F).map a)⟦(1 : ℤ)⟧' ≫ f ≫ c) =
      (forget F).mapDerivedCategory.map a ≫ cyclicDerivedFreeShiftedHomEquiv F M N f ≫
        ((forget F).mapDerivedCategory.map c)⟦(-1 : ℤ)⟧' := by
  simp only [cyclicDerivedFreeShiftedHomEquiv_apply,
    cyclicDerivedFreeFunctor, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  rw [← Functor.commShiftIso_hom_naturality]
  rfl

omit [IsGrothendieckAbelian.{v} C] in
/-- The cyclic action is a bijection in every degree: it is the map of an equivalence,
conjugated by the structure and shift isomorphisms.
Source: the invertible action in the free-resolution calculation
(blueprint: lem-sf-cyclic-free-hom-coordinates). -/
theorem cyclicDerivedHomAction_bijective (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) :
    Function.Bijective (cyclicDerivedHomAction F M N r) := by
  let e : (F.mapDerivedCategory.obj ((forget F).mapDerivedCategory.obj N))⟦r⟧ ≅
      ((forget F).mapDerivedCategory.obj N)⟦r⟧ :=
    (shiftFunctor _ r).mapIso ((cyclicDerivedStructure F).app N)
  let k : F.mapDerivedCategory.obj (((forget F).mapDerivedCategory.obj N)⟦r⟧) ≅
      ((forget F).mapDerivedCategory.obj N)⟦r⟧ :=
    (F.mapDerivedCategory.commShiftIso r).app _ ≪≫ e
  have h := (Iso.homCongr ((cyclicDerivedStructure F).app M) k).bijective.comp
    ((Functor.FullyFaithful.ofFullyFaithful F.mapDerivedCategory).map_bijective
      ((forget F).mapDerivedCategory.obj M) (((forget F).mapDerivedCategory.obj N)⟦r⟧))
  have heq : (cyclicDerivedHomAction F M N r : _ → _) =
      fun f ↦ Iso.homCongr ((cyclicDerivedStructure F).app M) k
        (F.mapDerivedCategory.map f) := by
    funext f
    simp [cyclicDerivedHomAction, Iso.homCongr, k, e, Preadditive.leftComp,
      Preadditive.rightComp, Category.assoc]
  rw [heq]
  exact h

end CategoryTheory.Endofunctor.IsoAlgebra

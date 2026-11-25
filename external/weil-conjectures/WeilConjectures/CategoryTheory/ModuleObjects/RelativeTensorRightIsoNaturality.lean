/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-!
# Naturality of the comparison of the relative tensor products

The comparison `Mod.relativeTensorRightIso N : Mod.tensorLeft N ≅ tensorRight N` between the
coequalizer relative tensor product and the monoidal tensor product of module objects is
compatible with the quotient maps (`Mod.tensorπ_relativeTensorRightIso_hom`) and natural in `N`
(`Mod.tensorLeftMap_relativeTensorRightIso_hom`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] in
/-- On the quotient map `M ⊗ N ⟶ M ⊗_R N`, the comparison `relativeTensorRightIso` is the
quotient map of the monoidal tensor product. -/
@[reassoc]
lemma tensorπ_relativeTensorRightIso_hom (M N : Mod C R) :
    tensorπ M N ≫ ((relativeTensorRightIso N).hom.app M).hom = tensorObjπ M N := by
  have h : colimit.ι ((tensorLeftDiagram R N).flip.obj M) WalkingParallelPair.one ≫
      (relativeTensorRightIso N).hom.app M = relativeTensorπ M N := by
    simp [relativeTensorRightIso, HasColimit.ι_isoOfNatIso_hom_assoc, relativeTensorCofork]
  exact congrArg Mod.Hom.hom h

omit [MonoidalPreadditive C] in
/-- The comparison `relativeTensorRightIso` is natural in the module being tensored with. -/
lemma tensorLeftMap_relativeTensorRightIso_hom {N N' : Mod C R} (f : N ⟶ N') :
    tensorLeftMap f ≫ (relativeTensorRightIso N').hom =
      (relativeTensorRightIso N).hom ≫ (tensoringRight _).map f := by
  apply NatTrans.ext
  funext P
  apply tensorLeft_obj_hom_ext
  simp only [NatTrans.comp_app, Mod.comp_hom']
  rw [tensorπ_tensorLeftMap_assoc, tensorπ_relativeTensorRightIso_hom,
    tensorπ_relativeTensorRightIso_hom_assoc]
  exact (tensorObjπ_whiskerLeft f).symm

end CategoryTheory.Mod

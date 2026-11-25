/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Naturality of the zeroth derived augmentation in the functor

Source: Stacks Project, Tag 0156, zeroth right derived functor and its augmentation.
(blueprint: lem-weil-pbc-right-derived-zero-transformation)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- Source: Stacks Project, Tag 0156, construction of the zeroth right derived functor.
(blueprint: lem-weil-pbc-right-derived-zero-transformation)

Proof: On a chosen resolution P of M, the augmentation is the map into the
zeroth cycles followed by cycles-to-homology and the derived comparison.
The induced map on homology commutes with cycles-to-homology. The induced
map on cycles commutes with the augmentations: cancel their monomorphic
inclusions into the degree-zero terms and use naturality of α at P.ι⁰.
Cancel the target derived comparison and combine these equalities. -/
theorem rightDerived_zero_transformation
    {A B : C ⥤ D} [A.Additive] [B.Additive] (α : A ⟶ B) (M : C) :
    A.toRightDerivedZero.app M ≫ (α.rightDerived 0).app M =
      α.app M ≫ B.toRightDerivedZero.app M := by
  let P := injectiveResolution M
  let φ := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app P.cocomplex
  have hcycles : P.toRightDerivedZero' A ≫ HomologicalComplex.cyclesMap φ 0 =
      α.app M ≫ P.toRightDerivedZero' B := by
    rw [← cancel_mono (HomologicalComplex.iCycles _ 0)]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
    exact α.naturality (P.ι.f 0)
  rw [P.toRightDerivedZero_eq A, P.toRightDerivedZero_eq B,
    P.rightDerived_app_eq α 0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change P.toRightDerivedZero' A ≫ HomologicalComplex.homologyπ _ 0 ≫
    HomologicalComplex.homologyMap φ 0 ≫ (P.isoRightDerivedObj B 0).inv = _
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc, hcycles]
  simp only [Category.assoc]
  rfl

end CategoryTheory

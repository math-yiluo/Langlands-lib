/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # HomComplexUnitEvaluation

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: def-sc-hom-complex-unit-evaluation).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace CategoryTheory

variable {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})

/-- The structure sheaf concentrated in degree zero. -/
noncomputable abbrev homComplexUnitSource :=
  (CochainComplex.singleFunctor
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) 0).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- The Hom-complex functor with source the unit in degree zero. -/
noncomputable abbrev homComplexUnitFunctor :=
  (homComplexFunctor (R := R)).obj (op (homComplexUnitSource J R))

set_option backward.isDefEq.respectTransparency true in
/-- Projection to the zero source degree followed by evaluation at one.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: def-sc-hom-complex-unit-evaluation).
The projection is the specified projection of the actual Hom-complex construction;
transport the source degree zero along the single-complex isomorphism, then evaluate. -/
noncomputable def homComplexUnitEvaluation
    (M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℤ) :
    ((homComplexUnitFunctor J R).obj M).X n ⟶ M.X n := by
  let s : (homComplexUnitSource J R).X 0 ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  exact (Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)))
      (homComplexUnitSource J R) M n 0 n (by omega) ≫
    SheafOfModules.homObjMap.{u, u, u, u} (R := R) s.inv (𝟙 (M.X n)) ≫
      (SheafOfModules.homObjUnitIso (R := R) (M.X n)).hom

end CategoryTheory

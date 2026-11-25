/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit

/-!
# `H⁰` of the right derived functor, normalized by the derived unit

For a left exact additive functor `F : C ⥤ D`, the identification
`H⁰(RF(X[0])) ≅ F X` of
`CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso`
is compatible with the computation unit `F.rightDerivedFunctorUnitQ` on single complexes.
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [HasKInjectiveResolutions C]

/-- On a single complex, the computation unit is the single-object unit precomposed with
the comparison `F(X[0]) ≅ (F X)[0]`. -/
theorem rightDerivedFunctorUnitQ_single (X : C) :
    F.rightDerivedFunctorUnitQ ((HomologicalComplex.single C (.up ℤ) 0).obj X) =
      DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) ≫
        F.rightDerivedSingleUnit X := by
  simp only [DerivedCategory.Q_obj_single_obj, rightDerivedFunctorUnitQ, comp_obj,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_inv, Quotient.lift.isLift_hom, rightDerivedSingleUnit,
    mapCochainComplexSingleFunctor, HomotopyCategory.quotient_obj_singleFunctors_obj]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Functor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

/-- For a left exact `F`, the identification `H⁰(RF(X[0])) ≅ F X` normalized by the
computation unit: after `H⁰`, the unit on `X[0]` followed by it is the canonical map
`H⁰(F(X[0])) ≅ H⁰((F X)[0]) ≅ F X`. -/
theorem exists_homologyZero_iso_rightDerivedFunctorUnitQ [PreservesFiniteLimits F]
    [EnoughInjectives C] :
    ∃ e : (DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor) ⋙
        DerivedCategory.homologyFunctor D 0 ≅ F,
      ∀ X, (DerivedCategory.homologyFunctor D 0).map
          (F.rightDerivedFunctorUnitQ ((HomologicalComplex.single C (.up ℤ) 0).obj X)) ≫
            e.hom.app X =
        (DerivedCategory.homologyFunctor D 0).map
          (DerivedCategory.Q.map
            ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X)) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app (F.obj X) := by
  refine ⟨F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso, fun X ↦ ?_⟩
  rw [rightDerivedFunctorUnitQ_single, Functor.map_comp, Category.assoc]
  exact congrArg (_ ≫ ·) (F.rightDerivedSingleUnit_zero X)

end CategoryTheory.Functor

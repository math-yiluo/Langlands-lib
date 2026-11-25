/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-!
# The left derived functor on a flat object placed in degree zero

Let `F : C ⥤ D` be an additive functor from a monoidal abelian category with functorial flat
resolutions, preserving the quasi-isomorphisms between K-flat complexes, and `L(F)` its total
left derived functor (`CategoryTheory.Functor.leftDerivedFunctor`). A flat object `P` of `C`
placed in degree zero is K-flat (`CochainComplex.kFlat_single_obj_iff_flat`), so `L(F)` is
computed on it by applying `F`: `L(F)(P[0]) ≅ (F P)[0]`
(`CategoryTheory.Functor.leftDerivedFunctorSingleFunctorIsoOfFlat`).
-/

@[expose] public section

universe uC uD vC vD wC wD

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

/-- On a flat object `P` placed in degree zero, the total left derived functor of `F` is computed
by applying `F`: `L(F)(P[0]) ≅ (F P)[0]`. The complex `P[0]` is K-flat, so the counit of `L(F)`
is invertible at it (`Functor.isIso_leftDerivedFunctorCounit_app_of_kFlat`), and `F` commutes
with placing objects in degree zero (`HomologicalComplex.singleMapHomologicalComplex`). -/
noncomputable def leftDerivedFunctorSingleFunctorIsoOfFlat {P : C} (hP : ObjectProperty.flat P) :
    L(F).obj ((DerivedCategory.singleFunctor C 0).obj P) ≅
      (DerivedCategory.singleFunctor D 0).obj (F.obj P) :=
  haveI := F.isIso_leftDerivedFunctorCounit_app_of_kFlat _
    ((CochainComplex.kFlat_single_obj_iff_flat P 0).2 hP)
  L(F).mapIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app P ≪≫
      (DerivedCategory.quotientCompQhIso C).symm.app _) ≪≫
    asIso (F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj P))) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso D).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app P) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ D 0).symm.app _

end CategoryTheory.Functor

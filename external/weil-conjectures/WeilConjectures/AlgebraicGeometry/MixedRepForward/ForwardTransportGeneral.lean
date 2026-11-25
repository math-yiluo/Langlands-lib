/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.AlgebraicGeometry.MixedRepForward.FiniteCoefficientInstances
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorSheaf
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeCounit
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeCounitTransport

/-!
# The forward cochain tensor counit square for general coefficients

This is the coefficient-generic form of
`AlgebraicGeometry.ProEtale.MixedRepForward.forward_transport`.

## Implementation details

Stating the result for an abstract coefficient category keeps elaboration and kernel checking
cheap. The proof follows the same route as `forward_transport`.

## References

* Stacks Project, Tag 07A4, tensor pullback comparison
-/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor
section QuotientIdentities

universe w

private theorem quotient_tensor
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (P Q : CochainComplex C ℤ) :
    ((HomotopyCategory.quotient C (.up ℤ)).obj P ⊗
      (HomotopyCategory.quotient C (.up ℤ)).obj Q) =
      (HomotopyCategory.quotient C (.up ℤ)).obj (P ⊗ Q) := rfl

private theorem cochain_tensor_obj
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (P Q : CochainComplex C ℤ) :
    P ⊗ Q = HomologicalComplex.mapBifunctor P Q (curriedTensor C) (.up ℤ) := rfl

private theorem Qh_quotient_obj
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      DerivedCategory.Q.obj P := rfl

private theorem Qh_quotient_map
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := rfl

private theorem mapH_quotient
    {C D : Type*} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (P : CochainComplex C ℤ) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      (HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) := rfl

end QuotientIdentities

namespace AlgebraicGeometry.ProEtale
open AlgebraicGeometry Scheme
namespace MixedRepForward
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
variable {U X : Scheme.{u}} (j : U ⟶ X)
local notation "ShX" => Sheaf (Scheme.ProEt.topology X) A
local notation "ShU" => Sheaf (Scheme.ProEt.topology U) A
local notation "pull" => (j)^*[A]

/-- The derived pullback tensor comparison satisfies its forward counit square on arbitrary
complexes `P` and `Q`, for an arbitrary coefficient category. -/
theorem forward_transport_general
    (P Q : CochainComplex ShX ℤ) :
    ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
      A j).hom.app
      ((DerivedCategory.Q (C := ShX)).obj P)).app
      ((DerivedCategory.Q (C := ShX)).obj Q) ≫
      ((pull).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := ShX)).obj P) ≫
        (pull).mapDerivedCategoryFactors.hom.app P ⊗ₘ
       (pull).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := ShX)).obj Q) ≫
        (pull).mapDerivedCategoryFactors.hom.app Q) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := ShU))
        (((pull).mapHomologicalComplex (.up ℤ)).obj P)
        (((pull).mapHomologicalComplex (.up ℤ)).obj Q)) =
      L(pull).map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ShX)) P Q) ≫
      ((pull).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := ShX)).obj
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor ShX) (.up ℤ))) ≫
        (pull).mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor ShX) (.up ℤ))) ≫
      (DerivedCategory.Q (C := ShU)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          pull).app P).app Q) := by
  rw [CategoryTheory.Functor.leftDerivedFactors_eq_counit,
    CategoryTheory.Functor.leftDerivedFactors_eq_counit,
    CategoryTheory.Functor.leftDerivedFactors_eq_counit]
  rw [CategoryTheory.Functor.cochainLocalization_tensorator_eq,
    CategoryTheory.Functor.cochainLocalization_tensorator_eq]
  have h := leftDerivedUpperStarTensorComparison_app_app_fac
    (A := A) j
    ((HomotopyCategory.quotient ShX (.up ℤ)).obj P)
    ((HomotopyCategory.quotient ShX (.up ℤ)).obj Q)
  rw [leftDerivedUpperStarDerivedTensorCounit_app_app,
    derivedTensorLeftDerivedUpperStarCounit_app_app] at h
  dsimp only [Functor.whiskeringLeft₂, Functor.postcompose₂,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_obj] at h
  with_unfolding_all
    simpa only [leftDerivedUpperStarTensorNatIso_hom, tensorHom_def,
      mapH_quotient, quotient_tensor, cochain_tensor_obj,
      Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app,
      Qh_quotient_obj, Qh_quotient_map, Functor.comp_obj, Category.assoc, cast_eq] using h

end MixedRepForward
end AlgebraicGeometry.ProEtale

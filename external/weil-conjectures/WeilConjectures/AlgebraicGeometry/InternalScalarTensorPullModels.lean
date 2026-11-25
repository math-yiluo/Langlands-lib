/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorModel
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap

/-! # Common models for the normalized scalar and tensor pullback routes

Source: Stacks 06YY, 0G7E, 07A6; the integral proper-base-change proof (1), (3).
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
set_option allowUnsafeReducibility true
attribute [local reducible] AlgebraicGeometry.ProEtale.QuotientChange.L
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

/-- Exact restriction/pullback with the specified localization comparisons.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def scalarTensorRestrictPullIso (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    V a Y ⋙ L Λ f ≅ L Λ' f ⋙ V a X := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact Functor.isoWhiskerRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ' f) (V a X) ≪≫
    CondensedRing.derivedComapUpperStarIso a f ≪≫
    Functor.isoWhiskerLeft (V a Y)
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm |>.symm

/-- The exact restriction/single comparison for the regular coefficient.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def scalarTensorRegularRestriction (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (V a T).obj (𝟙_ (DerivedCategory (Modules Λ' T))) ≅ B a T :=
  cast (by rfl) <| (V₀ a T).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (Modules Λ' T) 0).obj
        (Mod.regular (condensedRingObj Λ' T))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (V₀ a T) (.up ℤ) 0).app
        (Mod.regular (condensedRingObj Λ' T)))

/-- Pullback of the restricted regular coefficient, including its unit comparison.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def scalarTensorRegularPullIso (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (L Λ f).obj (B a Y) ≅ B a X := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.upperStar Λ f).leftDerivedFunctor.mapIso
      (scalarTensorRegularRestriction a Y).symm ≪≫
    (scalarTensorRestrictPullIso a f).app (𝟙_ (DerivedCategory (Modules Λ' Y))) ≪≫
    (V a X).mapIso (CondensedRing.leftDerivedUpperStarUnitIso Λ' f) ≪≫
    scalarTensorRegularRestriction a X

/-- Compare the target of the scalar square to its ordinary homotopy tensor model.
Only the pulled-back variable needs to be K-flat for this map to be invertible.
Source: Stacks 06YY, 0G7E (auxiliary; not a blueprint node). -/
@[irreducible] def scalarTensorPullModelTarget (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :=
  (L Λ f).obj (DerivedCategory.Qh.obj P) ◁ (scalarTensorRegularPullIso a f).inv ≫
    Functor.tensorModelTargetWith (CondensedRing.upperStar Λ f) (L Λ f)
      (pullCounit (Λ := Λ) f) (B₀ a Y) P

/-- The common map: restricted scalar counit, pullback counit, and ordinary tensorator.
Every map is constructed, including for nonflat coefficient maps.
Source: Stacks 06YY, 0G7E (auxiliary; not a blueprint node). -/
@[irreducible] def scalarTensorPullModelMap (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :=
  Functor.tensorModelMapWith (CondensedRing.upperStar Λ f) (L Λ f)
    (pullCounit (Λ := Λ) f) (B₀ a Y) (D a Y ⋙ V a Y)
    (by unfold D; exact Mod.tensorPresentationDerivedCounit (coefficientMap a Y)) P

end AlgebraicGeometry.ProEtale.QuotientChange

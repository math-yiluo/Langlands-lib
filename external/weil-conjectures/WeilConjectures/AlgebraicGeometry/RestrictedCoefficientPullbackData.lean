/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
public import WeilConjectures.AlgebraicGeometry.ModuleRingedToposDerivedComparison

/-! # Constructed regular-coefficient pullback comparisons

The ordinary and exact derived comparisons are independent of the projection-mate theorem.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.QuotientChange
namespace AlgebraicGeometry.ProEtale.RestrictedCoefficientMate
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

/-- The ordinary restricted-regular pullback identification: restrict the regular
S-module after pullback and apply the specified monoidal unit comparison.
Source: blueprint rational proper-base-change proof (1), cartesian coefficients;
Stacks 07A4 (auxiliary; not a blueprint node). -/
def regularPullback₀ (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar R f).obj (B₀ a Y) ≅ B₀ a X :=
  (CondensedRing.comapUpperStarIso a f).symm.app _ ≪≫
    (V₀ a X).mapIso (Functor.Monoidal.εIso (CondensedRing.upperStar S f)).symm

/-- The canonical rho, using exact inverse image, its localization comparison and
its degree-zero comparison, followed by the ordinary cartesian identification.
Source: blueprint rational proper-base-change proof (1); Stacks 07A4 and 07A6
(auxiliary; not a blueprint node). -/
def regularPullback (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L R f).obj (B a Y) ≅ B a X := by
  unfold L CondensedRing.moduleObjectDerivedPullback
  exact (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).app (B a Y) ≪≫
    (CondensedRing.upperStar R f).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor _ 0).obj (B₀ a Y)) ≪≫
    DerivedCategory.Q.mapIso
      (((CondensedRing.upperStar R f).mapCochainComplexSingleFunctor 0).app (B₀ a Y) ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso (regularPullback₀ a f))

end AlgebraicGeometry.ProEtale.RestrictedCoefficientMate

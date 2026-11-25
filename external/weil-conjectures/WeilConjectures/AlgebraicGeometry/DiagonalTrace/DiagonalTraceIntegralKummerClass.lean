/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite

/-! # The integral finite Kummer composite, before comparing the two sites -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext comparisonUpperStar cartierProRootMap

/-- Evaluate the Yoneda composite of the line-bundle class and the actual tower
Kummer extension, then insert the finite root map. Every arrow is specified by
an existing construction; no lift or comparison equation is chosen.
Source: geometric tower classes proof (2), positive Kummer boundary.
(blueprint: def-sfb-diagonal-trace-integral-kummer-class). -/
def evaluatedIntegralKummerClass (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (hA : ((l ^ (n + 1) : ℕ) : A) = 0)
    (k : Kummer l T) (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) (P : T.Pic) :
    Ext.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((cartierForget A T).obj (geoCartierLine A (l ^ (n + 1)) hA T)) 2 :=
  (((Ext.homEquiv.symm (lineBundleClass T P)).comp k.exact.extClass
      (rfl : 1 + 1 = 2)).mapExactFunctor (abEvaluation T n)).comp
    (Ext.mk₀ (cartierProRootMap A (l ^ (n + 1)) hA T
      (pow_pos (Fact.out : l.Prime).pos _) hN)) (add_zero 2)

end AlgebraicGeometry.ProEtale.DiagonalTrace

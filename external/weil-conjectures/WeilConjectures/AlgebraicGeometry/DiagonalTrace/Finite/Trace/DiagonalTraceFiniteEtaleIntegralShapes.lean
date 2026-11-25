/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
import all WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
import all WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension

/-! # Transport squares for the finite étale boundary -/
@[expose] public noncomputable section
-- This module only holds private steps of `diagonalTrace_finiteEtale_integralBoundary`,
-- split off to bound the memory needed to check them; importers use `import all`.
set_option linter.privateModule false
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext HasDerivedCategory.standard
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  comparisonUpperStar diagonalFiniteToPadic diagonalForget SpTowerClasses.lineModule

open SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open WeilConjectures
attribute [local implicit_reducible] spCoefficientCommRings
  SpTowerShriek.tau Functor.ofOpSequence Functor.ofSequence
  SemilinearSections.evaluation
attribute [local irreducible] SemilinearSections.scalarExtensionSection
  cartierProRootMap

attribute [local semireducible] diagonalForget SpTowerClasses.lineModule

section IntegralBoundaryCalculation

attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] CategoryTheory.constantSheaf comparisonLowerStar
  Functor.sheafPushforwardContinuous Scheme.toProEt

attribute [local irreducible] Ext.comp Ext.mk₀ Ext.mk₀CompMk₀
  Ext.mapExactFunctor Ext.homEquiv diagonalForget SpTowerClasses.lineModule
attribute [local implicit_reducible] geoCartierLine
attribute [local instance 100000] integralAbDerived

-- Transport the first Chern arrow through the evaluation isomorphism.
-- The category `C` is pinned so that instance search picks the derived-category instance used
-- by `finiteEvaluationEquation`, rather than unification copying the one in the type of `f`.
private theorem evalShape
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y)) (n : ℕ)
    (f : (DerivedCategory.singleFunctor
        (Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y))) 0).obj
          (coefficient (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y))) ⟶
      ((DerivedCategory.singleFunctor
        (Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y))) 0).obj
          (lineModule l (ULift.{u} (Padic l)) c))⟦(2 : ℤ)⟧) :
    EvalShape
      ((DerivedCategory.singleFunctor.{u + 1} (DiagonalAb (diagonalSurface Y)) 0).mapIso
        ((evalIso l (diagonalSurface Y) r n).app
          (coefficient (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))))
      ((DerivedCategory.singleFunctor.{u + 1} (DiagonalAb (diagonalSurface Y)) 0).mapIso
        ((evalIso l (diagonalSurface Y) r n).app (lineModule l (ULift.{u} (Padic l)) c)))
      (mapSingleArrow
        (C := Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
        (SpTowerShriek.ev l (ULift.{u} (Padic l)) (diagonalSurface Y) n ⋙
          finiteForget l (ULift.{u} (Padic l)) (diagonalSurface Y) n) (2 : ℤ) f)
      (mapSingleArrow
        (C := Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
        (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj (op n) ⋙
          diagonalForget l (diagonalSurface Y)) (2 : ℤ) f) :=
  mapSingleArrow_natIso
    (C := Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
    _ _ (evalIso l (diagonalSurface Y) r n).symm (2 : ℤ) f

-- Forget the supplied finite evaluation equation to abelian sheaves.
private theorem forgetShape
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y)) (n : ℕ)
    (f : (DerivedCategory.singleFunctor
        (Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y))) 0).obj
          (coefficient (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y))) ⟶
      ((DerivedCategory.singleFunctor
        (Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y))) 0).obj
          (lineModule l (ULift.{u} (Padic l)) c))⟦(2 : ℤ)⟧)
    (y : Ext (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y))
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1)) (cartierResidue_cast l (n + 1))
        (diagonalSurface Y)) 2)
    (aco : (r.F.obj (coefficient (diagonalSurface Y)
        (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))).obj (op n) ≅
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y)))
    (ali : (r.F.obj (lineModule l (ULift.{u} (Padic l)) c)).obj (op n) ≅
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1)) (cartierResidue_cast l (n + 1))
          (diagonalSurface Y)))
    (hb : finiteEvaluationEquation r.F (diagonalFiniteToPadic l n (diagonalSurface Y)) n
      aco ali f y) :
    ForgetShape
      ((DerivedCategory.singleFunctor.{u + 1} (DiagonalAb (diagonalSurface Y)) 0).mapIso
        ((diagonalForget l (diagonalSurface Y)).mapIso aco))
      ((DerivedCategory.singleFunctor.{u + 1} (DiagonalAb (diagonalSurface Y)) 0).mapIso
        ((diagonalForget l (diagonalSurface Y)).mapIso ali))
      (mapSingleArrow
        (C := Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
        (r.F ⋙ (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj (op n) ⋙
          diagonalForget l (diagonalSurface Y)) (2 : ℤ) f)
      (mapSingleArrow (diagonalFiniteToPadic l n (diagonalSurface Y) ⋙
        diagonalForget l (diagonalSurface Y)) (2 : ℤ) y.hom) :=
  forgottenFiniteEquation r.F (diagonalFiniteToPadic l n (diagonalSurface Y))
    (diagonalForget l (diagonalSurface Y)) n aco ali f y hb

-- Transport the finite étale class through the finite forgetful comparison.
private theorem cartierShape
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)] (n : ℕ)
    (y : Ext (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y))
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1)) (cartierResidue_cast l (n + 1))
        (diagonalSurface Y)) 2) :
    CartierShape
      ((DerivedCategory.singleFunctor.{u + 1} (DiagonalAb (diagonalSurface Y)) 0).mapIso
        ((diagonalFiniteForgetIso l n (diagonalSurface Y)).app
          (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y))))
      ((DerivedCategory.singleFunctor.{u + 1} (DiagonalAb (diagonalSurface Y)) 0).mapIso
        ((diagonalFiniteForgetIso l n (diagonalSurface Y)).app
          (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
            (cartierResidue_cast l (n + 1)) (diagonalSurface Y))))
      (mapSingleArrow (diagonalFiniteToPadic l n (diagonalSurface Y) ⋙
        diagonalForget l (diagonalSurface Y)) (2 : ℤ) y.hom)
      (mapSingleArrow (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)) (2 : ℤ)
        y.hom) :=
  mapSingleArrow_natIso _ _ (diagonalFiniteForgetIso l n (diagonalSurface Y)) (2 : ℤ) y.hom

end IntegralBoundaryCalculation

end AlgebraicGeometry.ProEtale.DiagonalTrace

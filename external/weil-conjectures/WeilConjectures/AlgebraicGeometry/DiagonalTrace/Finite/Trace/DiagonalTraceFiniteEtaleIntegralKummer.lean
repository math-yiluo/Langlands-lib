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

/-! # The integral Kummer class of the finite étale boundary -/
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

private theorem integralImage (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0)
    (b : Ext (Etale.ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2) :
    (Ext.mk₀ (siteIntegralGenerator A T)).comp
      ((finiteEtaleProImage A T N hA b).mapExactFunctor (cartierForget A T))
      (zero_add 2) =
    Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison T).inv
      ((Etale.ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2
        (Etale.ordinaryFiniteExtHomEquiv A T _ _ 2 b)).mapExactFunctor
          (comparisonUpperStar AddCommGrpCat.{u + 1} T))
      ((forgetComparisonIso A T).hom.app (Scheme.finiteEtaleTateLine T N A hA)) := by
  have hn := Ext.mapExactFunctor_square
    (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (comparisonUpperStar AddCommGrpCat.{u + 1} T)
    (Etale.RawModuleScalarComparison.forget A T) (cartierForget A T)
    (forgetComparisonIso A T) b
  rw [Etale.ordinaryFiniteClass_extHomEquiv]
  simp only [Etale.ordinaryFiniteExtClassCore, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀CompMk₀]
  rw [finiteEtaleProImage_apply, Ext.mapExactFunctor_mk₀CompMk₀]
  unfold siteIntegralGenerator
  rw [Ext.mk₀_comp_mk₀CompMk₀]
  simp only [Category.assoc, ← (cartierForget A T).map_comp,
    Iso.hom_inv_id, (cartierForget A T).map_id]
  simp only [Ext.mk₀CompMk₀, finiteEtaleLineIso, Iso.refl_hom,
    (cartierForget A T).map_id, Ext.comp_mk₀_id]
  simp only [← Ext.mk₀_comp_mk₀, Ext.comp_assoc]
  erw [Ext.mk₀_id_comp, ← hn]

private theorem kummerComposite_hom {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasExt C]
    (s : ShortComplex C) (hs : s.ShortExact) {X : C} (β : Ext X s.X₃ 1) :
    (β.comp hs.extClass (rfl : 1 + 1 = 2)).hom = kummerComposite s hs β.hom := by
  simp only [kummerComposite, Ext.comp_hom, hs.extClass_hom, ShiftedHom.comp,
    Int.natCast_add, Int.natCast_one, shiftFunctorAdd'_eq_shiftFunctorAdd]

private def evaluatedTowerBoundary
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ)
    (k : Kummer l T) (P : T.Pic) :
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((abEvaluation T n).obj (integers T)) ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
        ((abEvaluation T n).obj (roots l T)))⟦(2 : ℤ)⟧ :=
  -- Pinning `C` and `D` keeps the `Ab T` and `DiagonalAb T` spellings of the argument type,
  -- so the kernel does not reconcile the spellings under `Quiver.Hom`.
  mapSingleArrow (C := Ab T) (D := DiagonalAb T) (abEvaluation T n) (2 : ℤ)
    (kummerComposite (C := Ab T) (ShortComplex.mk k.inclusion k.power k.zero) k.exact
      (lineBundleClass T P))

private theorem kummerClass_hom_generic {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt C] [HasExt D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (s : ShortComplex C) (hs : s.ShortExact) {X : C} (x : Ext X s.X₃ 1)
    {Z : D} (g : F.obj s.X₁ ⟶ Z) :
    (((x.comp hs.extClass (rfl : 1 + 1 = 2)).mapExactFunctor F).comp
      (Ext.mk₀ g) (add_zero 2)).hom =
      mapSingleArrow F (2 : ℤ) (kummerComposite s hs x.hom) ≫
        ((DerivedCategory.singleFunctor D 0).map g)⟦(2 : ℤ)⟧' := by
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    ← SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext, kummerComposite_hom]
  rfl

private theorem evaluatedIntegralKummerClass_hom
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0) (k : Kummer l T)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) (P : T.Pic) :
    (evaluatedIntegralKummerClass l T A n hA k hN P).hom =
      evaluatedTowerBoundary l T n k P ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierProRootMap A (l ^ (n + 1)) hA T
            (pow_pos (Fact.out : l.Prime).pos _) hN))⟦(2 : ℤ)⟧' := by
  have h := kummerClass_hom_generic (C := Ab T) (D := DiagonalAb T) (abEvaluation T n)
    (ShortComplex.mk k.inclusion k.power k.zero) k.exact
    (Ext.homEquiv.symm (lineBundleClass T P) : Ext.{u + 2} (integers T) (units T) 1)
    (cartierProRootMap A (l ^ (n + 1)) hA T (pow_pos (Fact.out : l.Prime).pos _) hN)
  have hi : (Ext.homEquiv.symm (lineBundleClass T P) :
      Ext.{u + 2} (integers T) (units T) 1).hom = lineBundleClass T P :=
    Ext.homEquiv.apply_symm_apply _
  rw [hi] at h
  exact h

-- Specialize the finite Chern normalization to the evaluated tower boundary.
private theorem chernBoundary (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (n : ℕ) (P : (diagonalSurface Y).Pic) :
    (DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0).map
        (finiteQuotient l (ULift.{u} (Padic l)) (diagonalSurface Y) n) ≫
      mapSingleArrow
        (C := Systems (diagonalSurface Y) (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
        (SpTowerShriek.ev l (ULift.{u} (Padic l)) (diagonalSurface Y) n ⋙
          finiteForget l (ULift.{u} (Padic l)) (diagonalSurface Y) n) (2 : ℤ)
          (firstChern l (ULift.{u} (Padic l)) c P) ≫
      ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0).mapIso
        ((finiteForget l (ULift.{u} (Padic l)) (diagonalSurface Y) n).mapIso
          (lineEvaluation l (ULift.{u} (Padic l)) c n))).hom⟦(2 : ℤ)⟧' =
    evaluatedTowerBoundary l (diagonalSurface Y) n c.kummer P ≫
      ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0).map
        (finiteRootMap l (ULift.{u} (Padic l)) (diagonalSurface Y) n))⟦(2 : ℤ)⟧' := by
  -- Restate the normalization in this presentation: the kernel then compares the regular
  -- heads `mapSingleArrow` and `evaluatedTowerBoundary` instead of rechecking their bodies.
  have h : finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0).map
        (finiteQuotient l (ULift.{u} (Padic l)) (diagonalSurface Y) n))
      (((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface Y)) 0).map
        (finiteRootMap l (ULift.{u} (Padic l)) (diagonalSurface Y) n))⟦(2 : ℤ)⟧')
      (mapSingleArrow (finiteForget l (ULift.{u} (Padic l)) (diagonalSurface Y) n) (2 : ℤ)
        (evaluatedChern l (ULift.{u} (Padic l)) c P n))
      (evaluatedTowerBoundary l (diagonalSurface Y) n c.kummer P) := hc P n
  obtain ⟨α, β', hα, hβ, hN⟩ := h
  obtain rfl := eq_of_heq hα
  obtain rfl := eq_of_heq hβ
  simp only [evaluatedChern, mapSingleArrow_postcompose,
    mapSingleArrow_composite] at hN
  exact hN

end IntegralBoundaryCalculation

end AlgebraicGeometry.ProEtale.DiagonalTrace

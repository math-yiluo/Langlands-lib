/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteEvaluatedKummerComposite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralRootClass
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralClassEquations
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralRootBoundaryEquation
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteKummerComparisonComposite

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-compared-kummer-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local instance 100001] finiteIntegralTowerDerived finiteIntegralTowerExt
  finiteIntegralAbDerived finiteIntegralAbExt
  finiteIntegralEtaleDerived finiteIntegralEtaleExt

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison
  HasDerivedCategory.ofIsGrothendieckAbelian HomologicalComplex.quasiIso

/-- The comparison morphism of Kummer sequences transports the Picard boundary.
Source: Stacks 03PL and naturality of short-exact extension classes
(blueprint: lem-sfb-finite-compared-kummer-boundary). -/
theorem finiteComparedKummerBoundary (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (L : T.Pic) :
    @Eq (FiniteIntegralBoundaryArrow l T n)
      (finiteEvaluatedKummerComposite l T k n (lineBundleEtaleClass T L))
      (finiteIntegralRootClass l T n
        (T.kummerδ₁ (l ^ (n + 1)) hT (Scheme.Pic.toCohomologicalPicardGroup T L))) := by
  rw [finiteEvaluatedKummerComposite_eq, finiteLineBundleEtaleClass_eq,
    finiteIntegralRootClass_boundary_eq]
  exact finiteKummerComparison_composite l T k n hT (integerComparison T).inv
    (Scheme.Pic.toCohomologicalPicardGroup T L)

end AlgebraicGeometry.ProEtale.SpTowerClasses

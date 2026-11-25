/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-evaluated-kummer-composite).
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
  finiteIntegralAbDerived finiteIntegralAbExt finiteIntegralEtaleDerived finiteIntegralEtaleExt

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- The evaluated connecting composite with a specified degree-one input.
Source: exact evaluation of the Kummer sequence
(blueprint: def-sfb-finite-evaluated-kummer-composite). -/
def finiteEvaluatedKummerComposite (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ)
    (a : FiniteIntegralEvaluatedLineArrow T n) :
    FiniteIntegralBoundaryArrow l T n :=
  kummerComposite (C := DiagonalAb T)
    ((ShortComplex.mk k.inclusion k.power k.zero).map (abEvaluation T n))
    (k.exact.map_of_exact (abEvaluation T n)) a

/-- The cached connecting composite is its actual defining composite.
Source: exact evaluation of the tower Kummer sequence
(blueprint: def-sfb-finite-evaluated-kummer-composite). -/
theorem finiteEvaluatedKummerComposite_eq (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ)
    (a : FiniteIntegralEvaluatedLineArrow T n) :
    finiteEvaluatedKummerComposite l T k n a =
      kummerComposite (C := DiagonalAb T)
        ((ShortComplex.mk k.inclusion k.power k.zero).map (abEvaluation T n))
        (k.exact.map_of_exact (abEvaluation T n)) a := by rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses

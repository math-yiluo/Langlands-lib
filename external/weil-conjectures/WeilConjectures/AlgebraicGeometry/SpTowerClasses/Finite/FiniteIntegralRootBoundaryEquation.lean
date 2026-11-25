/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralRootClass

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-integral-root-boundary-equation).
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

/-- Exact comparison of the positive Kummer boundary is comparison of the
Yoneda composite, for any units extension. Source: Stacks 03PL and realization
of the Kummer connecting homomorphism
(blueprint: lem-sfb-finite-integral-root-boundary-equation).

Proof: apply the displayed integral roots comparison to the Yoneda composite.
The positive Kummer class is definitionally composition with the given
short-exact extension class, so this is the same input. -/
theorem finiteIntegralRootClass_boundary_eq (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (n : ℕ) (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    (x : Sheaf.H T.gmSheaf 1) :
    finiteIntegralRootClass l T n (T.kummerδ₁ (l ^ (n + 1)) hT x) =
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv ≫
        mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ)
          (x.comp (T.kummerSequence_shortExact (l ^ (n + 1)) hT).extClass
            (rfl : 1 + 1 = 2)).hom ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierRootsComparison T (l ^ (n + 1))))⟦(2 : ℤ)⟧' := by
  exact finiteIntegralRootClass_eq l T n
    (x.comp (T.kummerSequence_shortExact (l ^ (n + 1)) hT).extClass
      (rfl : 1 + 1 = 2))

end AlgebraicGeometry.ProEtale.SpTowerClasses

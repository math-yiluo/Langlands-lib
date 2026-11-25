/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteKummerSequenceComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-kummer-comparison-composite).
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
open FiniteExactArrow
attribute [local instance 100001] finiteIntegralTowerDerived finiteIntegralTowerExt
  finiteIntegralAbDerived finiteIntegralAbExt
  finiteIntegralEtaleDerived finiteIntegralEtaleExt

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- The actual comparison of Kummer short complexes preserves the boundary
composite of any degree-one extension and any source normalization.
Source: Stacks 03PL, short-exact extension naturality and Yoneda associativity
(blueprint: lem-sfb-finite-kummer-comparison-composite).

Proof: apply the generic short-exact comparison formula to the etale Kummer
sequence, the evaluated tower sequence and finiteKummerSequenceComparison.
Its first and third components are exactly the Cartier roots and units maps.
The formula is natural for every extension and source map. -/
theorem finiteKummerComparison_composite (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤)))
    {M : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} {Z : DiagonalAb T}
    (i : Z ⟶ (comparisonUpperStar AddCommGrpCat.{u + 1} T).obj M)
    (x : Ext.{u + 1} M T.gmSheaf 1) :
    kummerComposite
        ((ShortComplex.mk k.inclusion k.power k.zero).map (abEvaluation T n))
        (k.exact.map_of_exact (abEvaluation T n))
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map i ≫
          mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (1 : ℤ) x.hom ≫
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            (cartierUnitsComparison T))⟦(1 : ℤ)⟧') =
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map i ≫
        mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ)
          (x.comp (T.kummerSequence_shortExact (l ^ (n + 1)) hT).extClass
            (rfl : 1 + 1 = 2)).hom ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierRootsComparison T (l ^ (n + 1))))⟦(2 : ℤ)⟧' := by
  exact kummerComposite_comparison (comparisonUpperStar AddCommGrpCat.{u + 1} T)
    (T.kummerSequence_shortExact (l ^ (n + 1)) hT)
    (k.exact.map_of_exact (abEvaluation T n))
    (finiteKummerSequenceComparison l T k n) i x

end AlgebraicGeometry.ProEtale.SpTowerClasses

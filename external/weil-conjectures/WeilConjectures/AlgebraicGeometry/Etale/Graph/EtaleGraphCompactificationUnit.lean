/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-! # The graph comparison and the right-derived unit -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor canonicalEtaleCompactSupportComparison

/-- The inverse graph comparison is normalized by the right-derived unit for the proper
leg of the compactification.
Source: SGA 4 XVII 6.2.11 and Stacks Project, Tag 0F4L.
(blueprint: lem-pur-graph-compactification-unit).

Proof in words: the canonical etale comparison is the inverse of the explicitly
constructed derived graph map. Its inverse is therefore that graph map itself.
Apply the homotopy component formula of compactSupportDerivedComparison. Its first
factor is descent of exact sum extension, its second factor is the degreewise sheaf
graph map, and its remaining three factors are precisely the canonical comparison
unit for exact open extension followed by the right-derived proper direct image.
Expanding that unit gives the asserted equation on every homotopy object, without
choosing a resolution or imposing boundedness. -/
theorem graph_compactification_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Z : Scheme.{u}} [IsNoetherian W] [IsNoetherian Z]
    (b : W ⟶ Z) [Etale b] [IsSeparated b] (c : Compactification b)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (canonicalEtaleCompactSupportComparison A b c).inv.app (DerivedCategory.Qh.obj J) =
      (Functor.mapDerivedCategoryFactorsh
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance)).hom.app J ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (etaleCompactificationGraphMap A b c) (.up ℤ)).app J) ≫
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
        (lowerStar (ModuleCat.{u + 1} A) c.g)).app J := by
  unfold canonicalEtaleCompactSupportComparison
  change (compactSupportDerivedComparison A b c
    (etaleCompactificationGraphMap A b c)).app (DerivedCategory.Qh.obj J) = _
  rw [compactSupportDerivedComparison_app]
  simp only [compactSupportComparisonOnHomotopy, normalizationHomotopyComponent,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]

end AlgebraicGeometry.Etale

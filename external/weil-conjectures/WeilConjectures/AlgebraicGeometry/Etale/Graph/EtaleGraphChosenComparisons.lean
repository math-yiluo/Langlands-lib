/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement

/-! # Chosen compact-support comparisons used in graph composition

Source: Stacks Project, Tags 0F7I and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison rightDerivedLowerShriekIso
  mapDerivedCategoryOpenImmersionLowerShriekId rightDerivedLowerStarIdIso

/-- Compare the chosen compactification with the specified derived sum extension.
Source: SGA 4 XVII 6.2.11 (blueprint: def-pur-graph-chosen-etale-comparison). -/
@[irreducible]
noncomputable def graphChosenEtaleComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
    [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification f)).symm ≪≫
    canonicalEtaleCompactSupportComparison A f (HasCompactification.compactification f)

/-- Compute a proper map using its identity open immersion, then remove that identity.
Source: Stacks Project, Tags 0F7I and 0F7J
(blueprint: def-pur-graph-chosen-proper-comparison). -/
@[irreducible]
noncomputable def graphChosenProperComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] [HasCompactification p] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) p ≅
      rightDerivedLowerStar (ModuleCat.{u + 1} A) p :=
  (rightDerivedLowerShriekIso A (Compactification.ofIsProper p)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- Compute an open immersion using the identity proper map, then remove that identity.
Source: Stacks Project, Tags 0F7I and 0F7J
(blueprint: def-pur-graph-chosen-open-comparison). -/
@[irreducible]
noncomputable def graphChosenOpenComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] [HasCompactification j] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) j ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (Compactification.ofIsOpenImmersion j)).symm ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarIdIso A Y) ≪≫ Functor.rightUnitor _

end AlgebraicGeometry.Etale

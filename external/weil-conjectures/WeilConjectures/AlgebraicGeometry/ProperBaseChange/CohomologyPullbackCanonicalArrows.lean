/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit

/-!
# Named canonical Leray and derived restriction arrows

The original representative and comparison theorems are publicly imported. These
names expose precisely the right-hand composite of its derived-unit formula.

## References

* Stacks Project, Tags 01EZ, 01F8 and 08J6
* Stacks Project, Tags 01F8 and 0GJV
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Canonical Leray identification on bounded below derived global sections. -/
noncomputable def etaleLerayPlus {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus ⋙
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  @Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (lowerStar AddCommGrpCat.{u + 1} f)
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _ _ _
    (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f))
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f)

/-- Pullback of derived global sections, the derived unit followed by Leray. -/
noncomputable def etaleDerivedRestriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj K ⟶
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryPlus.obj K) :=
  (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus.unit.app K) ≫
    (etaleLerayPlus f).hom.app _

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.AlgebraicGeometry.DerivedUnitClassicalPullbackCoherence
import WeilConjectures.CategoryTheory.IdentityDerivedHomologyComparison

/-! # Derived-unit pullback and classical derived base change

Source: Stacks Project, Tag 01F8 and equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-derived-unit-classical-pullback)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- Homology of the derived-unit section map agrees with classical right-derived
base change, through the canonical single-complex comparisons.

Source: Stacks Project, Tag 01F8 and equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-derived-unit-classical-pullback)

Proof: the derived-unit and Leray description of pullback equals the right-derived
descendant of the underived section map, by the derived-unit formula. Deriving
that same section map as a square with identity functor on abelian groups gives
rightDerivedFunctorPlusBaseChange. Its defining unit compatibility and the
universal property of the right-derived functor identify these maps. Apply homology
and transport through the inverse-image/single-complex isomorphism. The definition
of rightDerivedBaseChange is precisely this transport followed by the classical
single-complex comparisons. Identity-functor comparisons cancel, yielding the
stated equality, including in degree zero. -/
theorem derivedUnit_classicalPullback {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let P := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let P' := (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let p := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      (P.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').derivedPlus.unit.app K) ≫
        (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (lowerStar AddCommGrpCat.{u + 1} g')
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _ _ _
          (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
            (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g'))
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g')).hom.app
            (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K))
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} g'
    let e : Γ ⋙ 𝟭 _ ⟶ L ⋙ Γ' :=
      (Functor.rightUnitor Γ).hom ≫ (Functor.leftUnitor Γ).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
    p ≫ (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        (P'.map ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app G)) ≫
        (Γ'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).hom.app
          (L.obj G) =
      (Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).hom.app G ≫
        (Functor.rightDerivedBaseChange e q).app G := by
  dsimp only
  rw [Functor.rightDerivedBaseChange_app]
  simp only [Functor.id_map, Iso.hom_inv_id_app_assoc]
  rw [Functor.identityDerivedHomologyComparison]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  rw [derivedUnit_classicalPullback_coherence]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry

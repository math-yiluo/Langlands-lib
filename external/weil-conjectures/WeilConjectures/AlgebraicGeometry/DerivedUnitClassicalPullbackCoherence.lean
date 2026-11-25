/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit

/-! # Total derived pullback coherence

Source: Stacks Project, Tag 01F8 and equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-derived-unit-classical-pullback-coherence)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- The total derived morphism underlying the classical pullback comparison.

Source: Stacks Project, Tag 01F8 and equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-derived-unit-classical-pullback-coherence)

Proof: identify both maps by the derived-unit formula and the defining unit
compatibility of the right-derived base-change morphism; the canonical identity
functor comparison is inserted on the source. To verify unit compatibility, use naturality of the
identity comparison to move it past the global-sections unit. Apply the
base-change unit equation and cancel the identity factorization comparison using
`mapDerivedCategoryPlusIdIso_hom_app_factorsh`. The remaining equality is the
levelwise underived section map. The universal property of right derivation and
`derivedCohomologyPullback_eq_derivedUnit` give the equality on every object.
This argument is valid on all bounded below objects and precedes homology. -/
theorem derivedUnit_classicalPullback_coherence {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    let P := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} g'
    let e : Γ ⋙ 𝟭 _ ⟶ L ⋙ Γ' :=
      (Functor.rightUnitor Γ).hom ≫ (Functor.leftUnitor Γ).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
    P.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').derivedPlus.unit.app K) ≫
      (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (lowerStar AddCommGrpCat.{u + 1} g') Γ _ _ _ _
        (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g'))
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g')).hom.app
          (L.mapDerivedCategoryPlus.obj K) =
    (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1}).inv.app (P.obj K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange e).app K := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
  let L := upperStar AddCommGrpCat.{u + 1} g'
  let e : Γ ⋙ 𝟭 _ ⟶ L ⋙ Γ' :=
    (Functor.rightUnitor Γ).hom ≫ (Functor.leftUnitor Γ).inv ≫
      Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
  let α : Γ.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ Γ'.rightDerivedFunctorPlus :=
    (Functor.rightUnitor Γ.rightDerivedFunctorPlus).inv ≫
      Functor.whiskerLeft Γ.rightDerivedFunctorPlus (Functor.mapDerivedCategoryPlusIdIso _).inv ≫
      Functor.rightDerivedFunctorPlusBaseChange e
  let β := Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus
        ((Functor.leftUnitor Γ).inv ≫
          Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ Γ'))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapHomotopyCategoryPlus Γ'.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv Γ'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom
  have hα : α = Functor.rightDerivedDesc _ Γ.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso _) _ β := by
    apply Functor.rightDerived_ext _ Γ.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso _)
    rw [Functor.rightDerived_fac]
    ext M : 2
    simp only [α, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_inv_app]
    erw [Category.id_comp]
    have hn := (Functor.mapDerivedCategoryPlusIdIso AddCommGrpCat.{u + 1}).inv.naturality
      (Γ.rightDerivedFunctorPlusUnith.app M)
    simp only [Functor.id_map] at hn
    rw [reassoc_of% hn]
    have hf := NatTrans.congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id] at hf
    rw [hf]
    simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
    simp only [Iso.inv_hom_id_app_assoc]
    dsimp only [β]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id]
    rw [← Functor.map_comp_assoc]
    congr 2
  have h := Etale.derivedCohomologyPullback_eq_derivedUnit g' K
  dsimp only
  rw [← h]
  have ha := NatTrans.congr_app hα K
  simpa only [α, NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Category.id_comp] using ha.symm

end AlgebraicGeometry

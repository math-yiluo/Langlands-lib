/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.UnderivedGlobalGermExchange
import WeilConjectures.AlgebraicGeometry.DerivedPulledGlobalGermFac
import WeilConjectures.AlgebraicGeometry.DerivedGlobalGermUnitFac

/-! # Derived exchange and the canonical global germ

Source: Stacks Project, Tags 095T, 01F8, and 08J6.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive
noncomputable local instance instAB5OfSizeAddCommGrpCat_derivedGlobalGermExchange
    : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- The canonical derived global germ intertwines exchange with the derived unit.

Source: Stacks Project, etale-cohomology.tex, Tag 095T, final map-on-stalks paragraph;
cohomology.tex, Tag 01F8; sites-cohomology.tex, Remark 08J6.
(blueprint: lem-weil-pbc-derived-global-germ-exchange)

Proof: Represent K by a bounded below injective complex I. Replace the exact inverse
image of I by an injective complex J. By
`Etale.existsUnique_derivedBaseChangeMapPlus_comparison` and
`Etale.derivedBaseChangeMapPlus_eq_termwise`, exchange is underived exchange on I
followed by direct image of the replacement. After global sections,
Leray and the global germ identify this with the unit on I followed by replacement
and then the target global germ. Underived equality is the mate formula for exchange
and naturality of the global germ. The defining unit compatibility of right-derived
natural transformations and of the Leray comparison transports precisely this equality
to the derived category. The identification of the section-pullback morphism with
RΓ of the derived unit is `derivedCohomologyPullback_eq_derivedUnit`. Equivalently, use
right-derived extensionality to check equality after precomposing the unit on injective
complexes; that computation is the termwise equality just given. These comparisons are
natural, so the resulting equality holds for every bounded below derived object.
This is compatibility only; neither of the global germs is asserted invertible. -/
theorem derivedGlobalGerm_exchange
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedPulledGlobalGerm f g t).app K ≫
        (pointSmallEtale t).sheafFiber.mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) =
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').derivedPlus.unit.app K) ≫
        (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (lowerStar AddCommGrpCat.{u + 1} g')
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _ _ _
          (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
            (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g'))
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g')).hom.app
            (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K)) ≫
      (derivedGlobalGerm f' t).app
        (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K) := by
  let B := AddCommGrpCat.{u + 1}
  let H := Sheaf.Γ X.smallEtaleTopology B
  let L := (g')^*[B].mapDerivedCategoryPlus
  let R := lowerStar B g'
  have : (lowerStar (AddCommGrpCat.{u + 1}) g').PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g')
  let HR := H.rightDerivedFunctorPlus
  let S := (pointSmallEtale t).sheafFiber (A := B)
  let SR := S.mapDerivedCategoryPlus
  let e := Functor.rightDerivedFunctorPlusCompIso' R H
    (lowerStarCompGlobalSectionsIso B g')
  let δ := derivedPulledGlobalGerm f g t ≫
      Functor.whiskerRight (derivedBaseChangeMapPlus B sq.toCommSq) SR ≫
      (Functor.associator L (f')_*[B].rightDerivedFunctorPlus SR).hom
  let ε := (Functor.leftUnitor HR).inv ≫
      Functor.whiskerRight (upperStarLowerStarAdjunction B g').derivedPlus.unit HR ≫
      (Functor.associator L R.rightDerivedFunctorPlus HR).hom ≫
      Functor.whiskerLeft L e.hom ≫ Functor.whiskerLeft L (derivedGlobalGerm f' t)
  have h : δ = ε := by
    apply Functor.rightDerived_ext HR H.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso _) _ δ ε
    ext M : 2
    have ha := derivedPulledGlobalGerm_fac f f' g g' sq.toCommSq t M
    have hb := derivedGlobalGerm_unit_fac f f' g g' sq.toCommSq t M
    have hab := underivedGlobalGerm_exchange f f' g g' sq.toCommSq t
    dsimp only at ha hb hab
    rw [hab] at ha
    simpa only [δ, ε, e, H, L, R, HR, SR, B, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.leftUnitor_inv_app, Category.comp_id, Category.id_comp, Category.assoc]
      using ha.trans hb.symm
  have hk := NatTrans.congr_app h K
  simpa only [δ, ε, e, H, L, R, HR, SR, B, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.leftUnitor_inv_app, Category.comp_id, Category.id_comp, Category.assoc] using hk


end AlgebraicGeometry.Etale

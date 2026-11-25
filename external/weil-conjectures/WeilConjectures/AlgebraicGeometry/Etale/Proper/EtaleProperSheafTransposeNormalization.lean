/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperSheafTransposeUnitCalculus

/-! # Normal form of the derived etale transpose of a sheaf map -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction etaleLowerShriekUpperStarAdjunction
  upperStarLowerStarAdjunction Adjunction.mapDerivedCategoryAdjunction

/-- The exact-derived transpose of the sheaf-induced map is the homotopy
transpose and ordinary base-change mate followed by the target right-derived unit.
Source: Stacks Project Tags 0F7B and 0D6E, localization and mixed-mate unit identities.
(blueprint: lem-pur-proper-sheaf-transpose-normalization). -/
theorem properSheaf_transpose_normal
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) (v : V ⟶ Y) [Etale v]
    {f : W ⟶ Y} (c : Compactification f)
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    let Q := lowerStar (ModuleCat.{u + 1} A) q
    let L := etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance
    let _R := upperStar (ModuleCat.{u + 1} A) v
    let O := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
    let G := lowerStar (ModuleCat.{u + 1} A) c.g
    let T := upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)
    let P := lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)
    let a := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance
    let ad := derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) v inferInstance
    let β := baseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g v).toCommSq
    let βD := exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g v).toCommSq
    ad.homEquiv _ _ (L.mapDerivedCategoryFactorsh.hom.app
          ((Q.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O G).app J) ≫
        βD.app (O.mapDerivedCategory.obj (DerivedCategory.Qh.obj J)) =
      DerivedCategory.Qh.map
        ((a.mapHomotopyCategory (.up ℤ)).homEquiv
            ((Q.mapHomotopyCategory (.up ℤ)).obj J)
            ((G.mapHomotopyCategory (.up ℤ)).obj ((O.mapHomotopyCategory (.up ℤ)).obj J))
            ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J) ≫
          (NatTrans.mapHomotopyCategory β (.up ℤ)).app
            ((O.mapHomotopyCategory (.up ℤ)).obj J)) ≫
        P.rightDerivedFunctorUnit.app
          ((T.mapHomotopyCategory (.up ℤ)).obj ((O.mapHomotopyCategory (.up ℤ)).obj J)) ≫
        P.rightDerivedFunctor.map
          (T.mapDerivedCategoryFactorsh.inv.app ((O.mapHomotopyCategory (.up ℤ)).obj J) ≫
            T.mapDerivedCategory.map (O.mapDerivedCategoryFactorsh.inv.app J)) := by
  intro Q L R O G T P a ad β βD
  exact exactDerivedTranspose_baseChange_normal Q L R O G T P a ad
    (fun X => etale_unit_fac A v X) βD β
    (fun M => baseChange_unit_normal A c.g v M) τ J

end AlgebraicGeometry.Etale

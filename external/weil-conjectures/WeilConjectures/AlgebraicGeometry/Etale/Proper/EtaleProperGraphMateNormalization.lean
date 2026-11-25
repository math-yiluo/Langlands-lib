/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange
public import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperGraphDerivedMate

/-! # Exact-derived normalization of the graph adjunction mate -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction etaleLowerShriekUpperStarAdjunction
  upperStarLowerStarAdjunction Adjunction.mapDerivedCategoryAdjunction

/-- The ordinary open-extension graph map induces the derived graph adjunct.
The exact factors are retained explicitly, so this equality uses no support
normalization hypothesis. Source: Stacks Project Tag 0F7B and the ordinary graph
unit identity. (blueprint: lem-pur-proper-graph-mate-normalization). -/
theorem properGraph_mate_normal
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    {f : W ⟶ Y} (hf : f = q ≫ v) (c : Compactification f)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (ProperGraphTransfer.graph q v hf c)).homEquiv _ _).symm
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          c.i).unit.app (DerivedCategory.Qh.obj J) ≫
        (ProperGraphTransfer.graphUpperStarIso q v hf c A).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj J))) =
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
        (ProperGraphTransfer.graph q v hf c)).mapDerivedCategoryFactorsh.hom.app J ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A)
          (ProperGraphTransfer.graph q v hf c) (pullback.fst c.g v) c.i
          (ProperGraphTransfer.graph_fst q v hf c)) (.up ℤ)).app J) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategoryFactorsh.inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
          (.up ℤ) |>.obj J) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
              c.i).mapDerivedCategoryFactorsh.inv.app J) := by
  simpa only [derivedOpenImmersionLowerShriekUpperStarAdjunction,
    ProperGraphTransfer.graphUpperStarIso, Functor.mapDerivedCategoryTriangleIso]
    using graph_mate_canonical A q v hf c J

private lemma graph_comparison_unit_normal
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    {f : W ⟶ Y} (hf : f = q ≫ v) (c : Compactification f)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (lowerStar (ModuleCat.{u + 1} A)
        (ProperGraphTransfer.graph q v hf c)).rightDerivedFunctorUnit.app J ≫
      (ProperGraphTransfer.graphDerivedIso q v hf c A).hom.app (DerivedCategory.Qh.obj J) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (ProperGraphTransfer.graph q v hf c)).homEquiv (DerivedCategory.Qh.obj J)
          ((upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj J)))).symm
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
            c.i).unit.app (DerivedCategory.Qh.obj J) ≫
          (ProperGraphTransfer.graphUpperStarIso q v hf c A).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
              (DerivedCategory.Qh.obj J))) =
    DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
          (ProperGraphTransfer.graph q v hf c))).inv (.up ℤ)).app J ≫
        (NatTrans.mapHomotopyCategory
          (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A)
            (ProperGraphTransfer.graph q v hf c) (pullback.fst c.g v) c.i
            (ProperGraphTransfer.graph_fst q v hf c)) (.up ℤ)).app J ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
            upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v))) (.up ℤ)).inv.app J) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategoryFactorsh.inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
          (.up ℤ) |>.obj J) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
              c.i).mapDerivedCategoryFactorsh.inv.app J) := by
  simp only [comp_homotopy_inv, Category.comp_id]
  rw [← Category.assoc]
  erw [ProperGraphTransfer.graphDerivedIso_unit q v hf c A J]
  erw [properGraph_mate_normal A q v hf c J]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, DerivedCategory.Qh.map_comp]

end AlgebraicGeometry.Etale

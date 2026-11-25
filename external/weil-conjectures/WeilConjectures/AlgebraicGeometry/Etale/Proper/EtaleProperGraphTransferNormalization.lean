/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperGraphDerivedMate
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperGraphMateNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperDerivedCompositionUnit

/-! # Normal form of the proper clopen graph transfer -/

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

private lemma unit_transfer_normal
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (Q : C ⥤ D) (P : E ⥤ C) (QE : E ⥤ F) (RP : F ⥤ D)
    (η : P ⋙ Q ⟶ QE ⋙ RP)
    {X Y : E} {V : C} {M N K : F} {Z : D}
    (e : V ⟶ P.obj X) (h : X ⟶ Y) (ρ : V ⟶ P.obj Y)
    (u : Q.obj V ⟶ Z) (c : Z ⟶ RP.obj M)
    (k : QE.obj X ⟶ M) (d : M ⟶ N) (δ : N ⟶ K) (κ : QE.obj Y ⟶ K)
    (hc : u ≫ c = Q.map e ≫ η.app X ≫ RP.map k)
    (hg : k ≫ d ≫ δ = QE.map h ≫ κ)
    (hs : ρ = e ≫ P.map h) :
    u ≫ c ≫ RP.map (d ≫ δ) = Q.map ρ ≫ η.app Y ≫ RP.map κ := by
  rw [← Category.assoc, hc]
  simp only [Category.assoc, ← RP.map_comp]
  rw [hg, RP.map_comp]
  have hn := η.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← Q.map_comp_assoc, ← hs]

/-- The clopen graph transfer, precomposed with the right-derived unit, is the
ordinary sheaf graph map followed by the target right-derived unit and exact factors.
Source: Stacks Project Tags 0F7B and 0F4L; the graph and compositor unit identities.
(blueprint: lem-pur-proper-graph-transfer-normalization). -/
theorem properGraphTransfer_normal
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    {f : W ⟶ Y} (hf : f = q ≫ v) (c : Compactification f)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorUnit.app J ≫
        ProperGraphTransfer.transfer q v hf c A (DerivedCategory.Qh.obj J) =
    DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (lowerStarComp (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c)
          (pullback.snd c.g v) q (ProperGraphTransfer.graph_snd q v hf c).symm).inv
        (.up ℤ)).app J ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl
          (lowerStar (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c) ⋙
            lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v))) (.up ℤ)).inv.app J ≫
        ((lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).mapHomotopyCategory
          (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory
            (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
              (ProperGraphTransfer.graph q v hf c))).inv (.up ℤ)).app J ≫
            (NatTrans.mapHomotopyCategory
              (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A)
                (ProperGraphTransfer.graph q v hf c) (pullback.fst c.g v) c.i
                (ProperGraphTransfer.graph_fst q v hf c)) (.up ℤ)).app J ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl
              (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
                upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v))) (.up ℤ)).inv.app J)) ≫
      (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).rightDerivedFunctorUnit.app
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapHomotopyCategory
          (.up ℤ) |>.obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
            (.up ℤ) |>.obj J)) ≫
      (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).rightDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategoryFactorsh.inv.app
              ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
                (.up ℤ) |>.obj J) ≫
          (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.map
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
              c.i).mapDerivedCategoryFactorsh.inv.app J)) := by
  unfold ProperGraphTransfer.transfer
  exact unit_transfer_normal
    (DerivedCategory.Qh (C := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    ((lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).mapHomotopyCategory (.up ℤ))
    (DerivedCategory.Qh (C := Sheaf (pullback c.g v).smallEtaleTopology (ModuleCat.{u + 1} A)))
    ((lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).rightDerivedFunctor)
    ((lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).rightDerivedFunctorUnit)
    (((NatTrans.mapHomotopyCategory (lowerStarComp (ModuleCat.{u + 1} A)
      (ProperGraphTransfer.graph q v hf c) (pullback.snd c.g v) q (ProperGraphTransfer.graph_snd
      q v hf c).symm).inv (.up ℤ)).app J ≫ (Functor.mapHomotopyCategoryCompIso (Iso.refl
      (lowerStar (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c) ⋙ (lowerStar
      (ModuleCat.{u + 1} A) (pullback.snd c.g v)))) (.up ℤ)).inv.app J))
    (((NatTrans.mapHomotopyCategory ((asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u +
      1} A) (ProperGraphTransfer.graph q v hf c))).inv) (.up ℤ)).app J ≫
      (NatTrans.mapHomotopyCategory (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A)
      (ProperGraphTransfer.graph q v hf c) (pullback.fst c.g v) c.i
      (ProperGraphTransfer.graph_fst q v hf c)) (.up ℤ)).app J ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((openImmersionLowerShriek (ModuleCat.{u +
      1} A) c.i) ⋙ (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)))) (.up ℤ)).inv.app J))
    _
    ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorUnit.app J)
    ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c)
      (pullback.snd c.g v) q (ProperGraphTransfer.graph_snd q v hf c)).inv.app
      (DerivedCategory.Qh.obj J))
    ((lowerStar (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf
      c)).rightDerivedFunctorUnit.app J)
    ((ProperGraphTransfer.graphDerivedIso q v hf c A).hom.app (DerivedCategory.Qh.obj J))
    ((((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (ProperGraphTransfer.graph q v hf c)).homEquiv (DerivedCategory.Qh.obj J) ((upperStar
      (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
      (DerivedCategory.Qh.obj J)))).symm ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) c.i).unit.app (DerivedCategory.Qh.obj J) ≫
      (ProperGraphTransfer.graphUpperStarIso q v hf c A).hom.app ((openImmersionLowerShriek
      (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj (DerivedCategory.Qh.obj J)))))
    (((upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategoryFactorsh.inv.app
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory (.up ℤ)).obj J)
      ≫ (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactorsh.inv.app
      J)))
    (properDerivedComposition_inv_unit A (ProperGraphTransfer.graph q v hf c) (pullback.snd c.g
      v) q (ProperGraphTransfer.graph_snd q v hf c) J)
    (graph_comparison_unit_normal A q v hf c J)
    ((Category.assoc _ _ _).symm)

end AlgebraicGeometry.Etale

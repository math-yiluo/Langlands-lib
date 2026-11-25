/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleCompositorRawUnit
import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleSheafSupportMap
import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperSheafUnitGraphTranspose

/-! # The graph transpose of the compact-support compositor -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor canonicalEtaleCompactSupportComparison
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

private noncomputable def graphTransferNat
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] {f : W ⟶ Y} (hf : f = q ≫ v)
    (c : Compactification f) :
    rightDerivedLowerStar (ModuleCat.{u + 1} A) q ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory ⋙
          rightDerivedLowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v) := by
  let B := ModuleCat.{u + 1} A
  let t := ProperGraphTransfer.graph q v hf c
  let L := (openImmersionLowerShriek B t).mapDerivedCategory
  let I := (openImmersionLowerShriek B c.i).mapDerivedCategory
  let U := (upperStar B (pullback.fst c.g v)).mapDerivedCategory
  let P := rightDerivedLowerStar B (pullback.snd c.g v)
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction B t
  let m : 𝟭 _ ⟶ (I ⋙ U) ⋙ (upperStar B t).mapDerivedCategory :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B c.i).unit ≫
      Functor.whiskerLeft I (ProperGraphTransfer.graphUpperStarIso q v hf c A).hom
  let a : L ⟶ I ⋙ U :=
    (Functor.leftUnitor L).inv ≫ Functor.whiskerRight m L ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (I ⋙ U) adj.counit ≫ (Functor.rightUnitor _).hom
  exact (rightDerivedLowerStarCompOfEq B t (pullback.snd c.g v) q
      (ProperGraphTransfer.graph_snd q v hf c)).inv ≫
    Functor.whiskerRight (ProperGraphTransfer.graphDerivedIso q v hf c A).hom P ≫
    Functor.whiskerRight a P

private theorem graphTransferNat_app
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] {f : W ⟶ Y} (hf : f = q ≫ v)
    (c : Compactification f) (K : DerivedCategoryModule A W) :
    (graphTransferNat A q v hf c).app K = ProperGraphTransfer.transfer q v hf c A K := by
  unfold graphTransferNat ProperGraphTransfer.transfer
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Category.id_comp,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  erw [(rightDerivedLowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).map_id]
  rw [Category.comp_id]
  rfl

/-- The transpose of compact-support composition is the clopen graph transfer.
Source: Stacks Project, Tags 0F7B, 0F7I, 0F7J; SGA 4 XVII 6.2.11.
(blueprint: lem-pur-proper-compositor-graph-transpose).

Proof in words: proper support constructs a normalized sheaf map into c. Compute the
chosen compositor after the raw direct-image unit on a compatible tower, using the
proper comparison, etale graph comparison, and open/proper interchange unit formulas;
then transport by common refinements. The sheaf graph-transpose theorem identifies
the transpose of this mixed unit, followed by proper base change, with the explicit
graph transfer after the same direct-image unit. Package the graph transfer and the
compositor transpose followed by base change as natural transformations. Adjunction
naturality gives equality after the right-derived unit on every homotopy object.
Uniqueness of transformations out of the right-derived functor gives equality on all
derived objects. The unit and support formulas also cover empty and identity maps.
No representative complex, derived-functor unit, or sheaf transformation tau occurs
in the assertion. -/
theorem properCompositor_graph_transpose
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    {f : W ⟶ Y} (hf : f = q ≫ v) [HasCompactification f]
    (c : Compactification f)
    (K : DerivedCategoryModule A W) :
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).homEquiv
        _ _ ((Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
            (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
            (graphChosenEtaleComparison A v).symm ≪≫
          unboundedEtaleLowerShriekCompIso A q v ≪≫
          unboundedEtaleLowerShriekCongr A hf.symm ≪≫
          (rightDerivedLowerShriekIso A c).symm).hom.app K) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) =
      ProperGraphTransfer.transfer q v hf c A K := by
  subst f
  let B := ModuleCat.{u + 1} A
  let F := lowerStar B q
  let G := etaleLowerShriek B v inferInstance
  let I := (openImmersionLowerShriek B c.i).mapDerivedCategory
  let adj := derivedEtaleLowerShriekUpperStarAdjunction B v inferInstance
  let E := (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
      G.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (rightDerivedLowerShriek B q)
      (graphChosenEtaleComparison A v).symm ≪≫
    unboundedEtaleLowerShriekCompIso A q v ≪≫ (rightDerivedLowerShriekIso A c).symm).hom
  let α : F.rightDerivedFunctor ⟶ I ⋙
      (upperStar B (pullback.fst c.g v)).mapDerivedCategory ⋙
        rightDerivedLowerStar B (pullback.snd c.g v) :=
    Functor.whiskerLeft F.rightDerivedFunctor adj.unit ≫
      Functor.whiskerRight E (upperStar B v).mapDerivedCategory ≫
      Functor.whiskerLeft I
        (exactDerivedBaseChangeMap B (IsPullback.of_hasPullback c.g v).toCommSq)
  have he : α = graphTransferNat A q v rfl c := by
    refine F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _ ?_
    apply NatTrans.ext
    funext J
    obtain ⟨τ, hτ⟩ := properEtaleSheafSupportMap_exists A q v
      (HasCompactification.compactification v) c
    have hu := properEtaleCompositor_raw_unit A q v c τ hτ J
    have ht := properSheafUnit_graph_transpose A q v rfl c τ hτ J
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [graphTransferNat_app]
    dsimp only [α, NatTrans.comp_app, Functor.whiskerLeft_app]
    have ht' : F.rightDerivedFunctorUnit.app J ≫
        (adj.homEquiv _ _ (E.app (DerivedCategory.Qh.obj J))) ≫
          (exactDerivedBaseChangeMap B
            (IsPullback.of_hasPullback c.g v).toCommSq).app
              (I.obj (DerivedCategory.Qh.obj J)) =
        F.rightDerivedFunctorUnit.app J ≫
          ProperGraphTransfer.transfer q v rfl c A (DerivedCategory.Qh.obj J) := by
      rw [← Category.assoc, ← adj.homEquiv_naturality_left]
      rw [hu]
      exact ht
    simpa only [Adjunction.homEquiv_unit, Functor.comp_obj, Functor.whiskerRight_app,
      rightDerivedLowerStar, Category.assoc] using ht'
  have hK := congr_app he K
  simp only [α, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    graphTransferNat_app] at hK
  simpa only [unboundedEtaleLowerShriekCongr, Iso.trans_refl, Iso.refl_trans,
    Adjunction.homEquiv_unit, B, F, G, I, adj, E, Functor.comp_obj,
    rightDerivedLowerStar, Category.assoc] using hK

end AlgebraicGeometry.Etale

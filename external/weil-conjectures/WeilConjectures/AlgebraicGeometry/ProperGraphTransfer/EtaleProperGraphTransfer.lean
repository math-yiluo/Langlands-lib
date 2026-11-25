/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-! # The clopen graph transfer for a proper map followed by an étale map

The graph in the pullback of a compactification is open, because the horizontal
projection is étale, and proper, because its composite with the vertical projection
is proper. Its extension by zero therefore equals its direct image. This gives a
concrete transfer without using compact-support composition.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
namespace ProperGraphTransfer

variable {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
  (v : V ⟶ Y) [Etale v] {f : W ⟶ Y} (hf : f = q ≫ v) (c : Compactification f)

/-- The map into the pullback of the proper part of the compactification along `v`. -/
noncomputable def graph : W ⟶ pullback c.g v :=
  pullback.lift c.i q (c.comm.symm.trans hf)

omit [IsProper q] [Etale v] in
@[simp] theorem graph_fst : graph q v hf c ≫ pullback.fst c.g v = c.i :=
  pullback.lift_fst _ _ _

omit [IsProper q] [Etale v] in
@[simp] theorem graph_snd : graph q v hf c ≫ pullback.snd c.g v = q :=
  pullback.lift_snd _ _ _

/-- A lift over an étale map whose composite is open is open. -/
instance graph_open : IsOpenImmersion (graph q v hf c) := by
  have : IsOpenImmersion (graph q v hf c ≫ pullback.fst c.g v) := by
    rw [graph_fst]
    infer_instance
  exact FormallyUnramified.isOpenImmersion_of_comp (pullback.fst c.g v) _

/-- Properness descends from the composite with the separated vertical projection. -/
instance graph_proper : IsProper (graph q v hf c) := by
  have : IsProper (graph q v hf c ≫ pullback.snd c.g v) := by
    rw [graph_snd]
    infer_instance
  exact IsProper.of_comp _ (pullback.snd c.g v)

variable (A : Type (u + 1)) [CommRing A]

/-- Extension by zero along this clopen graph is its direct image. -/
instance graph_comparison_isIso :
    IsIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (graph q v hf c)) :=
  isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range _ _
    (graph q v hf c).isClosedMap.isClosed_range

/-- The total derived direct image of the clopen graph is its exact extension by zero. -/
noncomputable def graphDerivedIso :
    rightDerivedLowerStar (ModuleCat.{u + 1} A) (graph q v hf c) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) (graph q v hf c)).mapDerivedCategory :=
  (Functor.rightDerivedFunctorNatIso
    (asIso (openImmersionLowerShriekToLowerStar _ (graph q v hf c))).symm) ≪≫
      (openImmersionLowerShriek _ (graph q v hf c)).rightDerivedFunctorIsoMapDerivedCategory

/-- The clopen graph comparison carries the ordinary derived unit to the exact
extension-by-zero unit. This fixes its normalization on every homotopy object. -/
theorem graphDerivedIso_unit
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (lowerStar (ModuleCat.{u + 1} A) (graph q v hf c)).rightDerivedFunctorUnit.app J ≫
        (graphDerivedIso q v hf c A).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (asIso (openImmersionLowerShriekToLowerStar
              (ModuleCat.{u + 1} A) (graph q v hf c))).inv (.up ℤ)).app J) ≫
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} A) (graph q v hf c)).mapDerivedCategoryFactorsh.inv.app J := by
  unfold graphDerivedIso
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc]
  erw [Functor.rightDerivedNatTrans_app _ _ _ _
    (HomotopyCategory.quasiIso _ (.up ℤ)) _ J]
  rw [Category.assoc]
  have h := congr_app (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) (graph q v hf c))) J
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom] using
    congrArg (DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (asIso (openImmersionLowerShriekToLowerStar
          (ModuleCat.{u + 1} A) (graph q v hf c))).inv (.up ℤ)).app J) ≫ ·) h

/-- The inverse-image compositor for the graph followed by the horizontal projection. -/
noncomputable def graphUpperStarIso :
    (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (graph q v hf c)).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso
    (upperStarComp _ (graph q v hf c) (pullback.fst c.g v) c.i
      (graph_fst q v hf c).symm) ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The graph transfer. First factor `Rq_*` through the proper graph, identify graph
pushforward with extension by zero, and take the adjunct of the unit for `c.i`.
No compact-support compositor or chosen comparison occurs in this construction. -/
@[irreducible] noncomputable def transfer (K : DerivedCategoryModule A W) :
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) q).obj K ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v)).obj
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K)) :=
  (rightDerivedLowerStarCompOfEq _ (graph q v hf c) (pullback.snd c.g v) q
      (graph_snd q v hf c)).inv.app K ≫
    (rightDerivedLowerStar _ (pullback.snd c.g v)).map
      ((graphDerivedIso q v hf c A).hom.app K ≫
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ (graph q v hf c)).homEquiv
          K _).symm
            ((derivedOpenImmersionLowerShriekUpperStarAdjunction _ c.i).unit.app K ≫
              (graphUpperStarIso q v hf c A).hom.app
                ((openImmersionLowerShriek _ c.i).mapDerivedCategory.obj K)))

omit [Etale v] in
/-- Proper base change detects equality after transposing along the étale adjunction. -/
theorem baseChange_isIso [Finite A] :
    IsIso (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback c.g v).toCommSq) := by
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite (IsPullback.of_hasPullback c.g v)
  rw [← exact_exchange_transport A (IsPullback.of_hasPullback c.g v).toCommSq]
  infer_instance

end ProperGraphTransfer
end AlgebraicGeometry.Etale

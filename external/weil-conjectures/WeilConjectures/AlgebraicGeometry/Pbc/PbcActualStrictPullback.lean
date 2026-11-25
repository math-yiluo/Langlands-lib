/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction

/-! # Functor and completion interface for the strict-tower pullback
The quotient tower, resolving pullback, derived limit and comparison
are retained. This interface supplies their functor and unit-compatible natural
isomorphism to the intrinsic completion reflector used by scalar comparisons.

## References

* Stacks 099N (2), (5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The functor underlying exactly the completedPullbackObject. -/
abbrev pbcActualStrictCompletedPull :=
  (completedReductionTower Y d ⋙ completedTowerPullback g d) ⋙ completedTowerRlim d X

/-- The actual compatible-family unit followed by derived limit of one strict
quotient augmentation. Its components are completedPullbackComparison. -/
def pbcActualStrictCompletedPullUnit :
    pbcActualDerivedPull g d ⟶ pbcActualStrictCompletedPull d g :=
  (pbcActualDerivedPull g d).rightUnitor.inv ≫
    whiskerLeft (pbcActualDerivedPull g d) (completedConstantRlimUnit d X) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight ((completedPullbackConstantIso g d).hom ≫
      whiskerRight (completedReductionTowerUnit d Y) (completedTowerPullback g d))
        (completedTowerRlim d X)

/-- The strict-tower formula and the completion reflector give the same completed
pullback, with the canonical quotient augmentation as their unit. -/
theorem pbcActualCompletedPullback_tower :
    ∃! e :
      ObjectProperty.ι (PbcIsIntrinsicallyComplete Y d) ⋙ pbcActualStrictCompletedPull d g ≅
        ObjectProperty.ι (PbcIsIntrinsicallyComplete Y d) ⋙ pbcActualCompletedPull g d,
      ∀ K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y d),
        (pbcActualStrictCompletedPullUnit d g).app K.obj ≫ e.hom.app K =
          (pbcActualCompletedPullUnit g d).app K.obj := by
  classical
  let L := pbcActualDerivedPull g d
  let R := completedTowerRlim d X
  let eL := pullbackDatumOrdinaryTransport g d
  let eT := pullbackDatumTowerTransport g d
  let τ := stratumReductionIso d g
  let t : completedReductionTower Y d ⋙ completedTowerPullback g d ≅
      L ⋙ completedReductionTower X d :=
    Functor.isoWhiskerLeft (completedReductionTower Y d) eT ≪≫ τ ≪≫
      Functor.isoWhiskerRight eL.symm (completedReductionTower X d)
  have ht (K : PbcCompletedDerived Y d) :
      ((completedPullbackConstantIso g d).hom.app K ≫
        (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
          t.hom.app K = (completedReductionTowerUnit d X).app (L.obj K) := by
    exact reductionAugmentationTransport
      (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (completedReductionTower Y d) (completedReductionTower X d)
      (completedOrdinaryPullback g d) (d.pull g)
      (completedTowerPullback g d) (d.towerPull g) eL eT
      (completedPullbackConstantIso g d) (d.derivedConstantPullbackIso g)
      (completedReductionTowerUnit d Y) (completedReductionTowerUnit d X) τ K
      (datumConstantComparison g d K) (stratumReduction_augmentation d g K)
  obtain ⟨c, hc⟩ := actualCompletion_quotient d X
  let b : pbcActualStrictCompletedPull d g ≅ pbcActualCompletedPull g d :=
    Functor.isoWhiskerRight t R ≪≫ Functor.associator L (completedReductionTower X d) R ≪≫
      Functor.isoWhiskerLeft L c.symm
  have hb (K : PbcCompletedDerived Y d) :
      (pbcActualStrictCompletedPullUnit d g).app K ≫ b.hom.app K =
        (pbcActualCompletedPullUnit g d).app K := by
    have hu : completedPullbackComparison g d K ≫ R.map (t.hom.app K) =
        d.completionUnit X (L.obj K) := by
      dsimp only [completedPullbackComparison]
      rw [Category.assoc, ← R.map_comp, ht, constantRlimUnit_eq]
      rfl
    simp only [pbcActualStrictCompletedPullUnit, pbcActualCompletedPullUnit, b,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
      Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.associator_hom_app, Functor.comp_obj, Iso.symm_hom]
    change completedPullbackComparison g d K ≫
      (R.map (t.hom.app K) ≫ c.inv.app (L.obj K)) =
        (pbcActualCompletionUnit d X).app (L.obj K)
    rw [← Category.assoc, hu, ← hc, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id]
  let e := Functor.isoWhiskerLeft (ObjectProperty.ι (PbcIsIntrinsicallyComplete Y d)) b
  refine ⟨e, fun K ↦ hb K.obj, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  apply (cancel_epi (e.inv.app K)).1
  apply (actualReflection d X (L.obj K.obj)
    ((pbcActualCompletedPull g d).obj K.obj)
    (pbcActualCompletedPull_isComplete g d K.obj)).injective
  have hi : (pbcActualCompletedPullUnit g d).app K.obj ≫ e.inv.app K =
      (pbcActualStrictCompletedPullUnit d g).app K.obj := by
    rw [← hb K.obj]
    change ((pbcActualStrictCompletedPullUnit d g).app K.obj ≫ e.hom.app K) ≫
      e.inv.app K = _
    rw [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  change (pbcActualCompletedPullUnit g d).app K.obj ≫
      (e.inv.app K ≫ e'.hom.app K) =
    (pbcActualCompletedPullUnit g d).app K.obj ≫
      (e.inv.app K ≫ e.hom.app K)
  rw [← Category.assoc, ← Category.assoc, hi, he']
  exact (hb K.obj).symm

end AlgebraicGeometry.Scheme

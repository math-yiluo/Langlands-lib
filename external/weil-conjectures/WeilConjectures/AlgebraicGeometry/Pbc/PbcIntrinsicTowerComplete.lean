/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Intrinsic completeness implies quotient-tower completeness

The intrinsic completion predicate implies invertibility of the quotient-tower
unit used by completed exchange. We specialize the library's unit-normalized
strict/intrinsic completed-pullback comparison to the identity morphism.
The remaining argument is categorical: constant towers are fully faithful on
derived categories, and pullback along the identity is isomorphic to identity.

## References

* Stacks Tag 099N
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory.Limits Opposite

private theorem identityComparison_isIso
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{u}) (K : PbcCompletedDerived T d)
    (hK : PbcIsIntrinsicallyComplete T d K) :
    IsIso (d.ordinaryToCompleted (𝟙 T) K) := by
  let M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete T d) := ⟨K, hK⟩
  let e := (pbcActualCompletedPullback_tower d (𝟙 T)).exists.choose
  have he := (pbcActualCompletedPullback_tower d (𝟙 T)).exists.choose_spec M
  let i := pbcActualCompletedPullIdIso d T
  have hi := (pbcActualCompletedPullIdIso_exists d T).exists.choose_spec M
  change (pbcActualStrictCompletedPullUnit d (𝟙 T)).app K ≫ e.hom.app M =
    (pbcActualCompletedPullUnit (𝟙 T) d).app K at he
  change (pbcActualCompletedPullUnit (𝟙 T) d).app K ≫ i.hom.app M =
    (pbcActualDerivedPullIdIso d T).hom.app K at hi
  have : IsIso ((pbcActualCompletedPullUnit (𝟙 T) d).app K) := by
    apply (isIso_comp_right_iff _ (i.hom.app M)).1
    rw [hi]
    infer_instance
  have : IsIso ((pbcActualStrictCompletedPullUnit d (𝟙 T)).app K) := by
    apply (isIso_comp_right_iff _ (e.hom.app M)).1
    rw [he]
    infer_instance
  have h := cbcDatumActualStrictTransport_unit d (𝟙 T) K
  have : IsIso ((cbcDatumOrdinaryTransport d (𝟙 T)).hom.app K ≫
      d.ordinaryToCompleted (𝟙 T) K) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((cbcDatumOrdinaryTransport d (𝟙 T)).hom.app K) _

private def evaluationConstantAdjunction (C : Type*) [Category C] :
    (CategoryTheory.evaluation ℕᵒᵖ C).obj (op 0) ⊣ (Functor.const ℕᵒᵖ : C ⥤ ℕᵒᵖ ⥤ C) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F X ↦
        { toFun := fun f ↦
            { app := fun n ↦ F.map (homOfLE (Nat.zero_le n.unop)).op ≫ f
              naturality := by
                intro n m a
                dsimp
                rw [← Category.assoc, ← F.map_comp]
                simp only [Category.comp_id]
                congr 1 }
          invFun := fun f ↦ f.app (op 0)
          left_inv := by intro f; simp
          right_inv := by
            intro f
            ext n
            exact (f.naturality (homOfLE (Nat.zero_le n.unop)).op).trans
              (Category.comp_id _) } }

private theorem constantUnit_isIso
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{u}) (K : d.derived T) :
    IsIso ((d.constantRlimAdjunction T).unit.app K) := by
  let C := reductionModules T (d.completedRing T)
  let E := (CategoryTheory.evaluation ℕᵒᵖ C).obj (op 0)
  let D := d.constantTower T
  let a : E.mapDerivedCategory ⊣ D.mapDerivedCategory :=
    ((evaluationConstantAdjunction C).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
      D.rightDerivedFunctorIsoMapDerivedCategory
  let e : D.mapDerivedCategory ⋙ E.mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
    Functor.mapDerivedCategoryCompIso D E ≪≫
      Functor.mapDerivedCategoryNatIso (Iso.refl (𝟭 C)) ≪≫
        Functor.mapDerivedCategoryIdIso C
  let ff := a.fullyFaithfulROfCompIsoId e
  let := ff.full
  let := ff.faithful
  infer_instance

private def towerPullIdentity
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{u}) : d.towerPull (𝟙 T) ≅ 𝟭 _ := by
  let C := reductionModules T (d.completedRing T)
  let p : proEtaleRingModulePullback (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T)) ≅ 𝟭 C :=
    (eqToIso (cbcDatumModulePull_eq d (𝟙 T))).symm ≪≫ pbcActualModulePullIdIso d T
  let e : d.towerModulePull (𝟙 T) ≅ 𝟭 (d.towers T) :=
    (Functor.whiskeringRight ℕᵒᵖ C C).mapIso p ≪≫ Functor.whiskeringRightObjIdIso
  exact Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _

private theorem towerComplete_of_identityComparison
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{u}) (K : d.derived T)
    (h : IsIso (d.ordinaryToCompleted (𝟙 T) K)) : d.TowerComplete T K := by
  let R := completedRlim T (d.completedRing T)
  let τ := (completedReductionAugmentation d T).app K
  have hu := constantUnit_isIso d T ((d.pull (𝟙 T)).obj K)
  have hm : IsIso (R.map ((d.towerPull (𝟙 T)).map τ)) := by
    change IsIso (_ ≫ R.map (_ ≫ _)) at h
    rw [Functor.map_comp] at h
    exact (isIso_comp_left_iff _ _).1 ((isIso_comp_left_iff _ _).1 h)
  have ht : IsIso (R.map τ) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (towerPullIdentity d T) R) τ).1 hm
  change IsIso (_ ≫ R.map τ)
  have := constantUnit_isIso d T K
  infer_instance

end

/-- Intrinsic Koszul completeness implies the canonical quotient-tower unit is invertible. -/
theorem pbcIntrinsicComplete_towerComplete
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{u}) (K : PbcCompletedDerived T d) :
    PbcIsIntrinsicallyComplete T d K → d.TowerComplete T K := by
  intro hK
  exact towerComplete_of_identityComparison d T K (identityComparison_isIso d T K hK)

end AlgebraicGeometry.Scheme

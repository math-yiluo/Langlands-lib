/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations
import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
import all WeilConjectures.CategoryTheory.ExactTowerAugmentedCounit.ExactTowerAugmentedCounitEvaluation
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionAugmentationCompatibility
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalized finite evaluations of strict quotient towers

The generic adic-datum calculations used by the immersion pullback comparison.

## References

* Stacks 03EL, 06YY and 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures
attribute [-instance] CategoryTheory.ringedConstantTowerAdditive
attribute [-instance] CategoryTheory.strictTowerConstantAdditive
attribute [-instance] CategoryTheory.strictTowerLimitAdditive
attribute [local irreducible] AlgebraicGeometry.Scheme.AdicCoefficients.ringSystem
  CategoryTheory.Limits.limit HasDerivedCategory.standard
namespace AlgebraicGeometry.Scheme

section GenericFinite

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (f : Y ⟶ X)

attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] Functor.mapHomotopyCategory
attribute [local irreducible] Functor.mapHomotopyCategoryFactors
attribute [local irreducible] completedReductionModuleTowerFunctor completedReductionTower
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh

private theorem conjugate_comp
    {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (e₀ : A₀ ⟶ B₀) (e₁ : A₁ ⟶ B₁) (e₂ : A₂ ⟶ B₂)
    (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂) (h : A₀ ⟶ A₂)
    (f' : B₀ ⟶ B₁) (g' : B₁ ⟶ B₂) (h' : B₀ ⟶ B₂)
    [Epi e₀] (hf : e₀ ≫ f' = f ≫ e₁) (hg : e₁ ≫ g' = g ≫ e₂)
    (hh : e₀ ≫ h' = h ≫ e₂) (hfg : f ≫ g = h) : f' ≫ g' = h' := by
  apply (cancel_epi e₀).1
  calc
    e₀ ≫ (f' ≫ g') = f ≫ (e₁ ≫ g') := by rw [← Category.assoc, hf, Category.assoc]
    _ = h ≫ e₂ := by rw [hg, ← Category.assoc, hfg]
    _ = e₀ ≫ h' := hh.symm

private theorem conjugate_square
    {C : Type*} [Category C] {P Q S T U V : C}
    (p : P ⟶ Q) (q : S ⟶ T) (a : Q ⟶ T) (b : U ⟶ V)
    (x : Q ⟶ U) (y : T ⟶ V) (c : P ⟶ S) (d : P ⟶ U) (e : S ⟶ V)
    [Epi p] (hp : c ≫ q = p ≫ a) (hx : p ≫ x = d) (hy : q ≫ y = e)
    (hc : c ≫ e = d ≫ b) : a ≫ y = x ≫ b := by
  apply (cancel_epi p).1
  calc
    p ≫ (a ≫ y) = c ≫ (q ≫ y) := by rw [← Category.assoc, ← hp, Category.assoc]
    _ = d ≫ b := by rw [hy, hc]
    _ = p ≫ (x ≫ b) := by rw [← hx, Category.assoc]

section ProjectionProofs

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
local instance siteSmall (T : Scheme.{u}) :
  EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance] reductionModulesHasDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryNatIso

-- Evaluate the adjoint transpose, then use constant/evaluation coherence.
attribute [local semireducible] completedReductionModuleTowerFunctor

-- The two normalized computing counits identify this with the tensor-unit map.
end ProjectionProofs

end GenericFinite

private theorem completion_general
    {A : Type (u + 1)} [CommRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedOrdinaryPullback g d).obj K) :
    ∃ α : completedPullbackObject g d K ≅
        intrinsicCompletion X d r a ha ((completedOrdinaryPullback g d).obj K) P eP,
      completedPullbackComparison g d K ≫ α.hom =
        intrinsicCompletionUnit X d r a ha ((completedOrdinaryPullback g d).obj K) P eP := by
  let eL := pullbackDatumOrdinaryTransport g d
  let eT := pullbackDatumTowerTransport g d
  let τ := stratumReductionIso d g
  let R := completedTowerRlim d X
  let t : (completedTowerPullback g d).obj ((completedReductionTower Y d).obj K) ≅
      (completedReductionTower X d).obj ((completedOrdinaryPullback g d).obj K) :=
    eT.app ((completedReductionTower Y d).obj K) ≪≫ τ.app K ≪≫
      (completedReductionTower X d).mapIso (eL.app K).symm
  have ht : ((completedPullbackConstantIso g d).hom.app K ≫
      (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
        t.hom = (completedReductionTowerUnit d X).app
          ((completedOrdinaryPullback g d).obj K) := by
    exact reductionAugmentationTransport
      (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (completedReductionTower Y d) (completedReductionTower X d)
      (completedOrdinaryPullback g d) (d.pull g)
      (completedTowerPullback g d) (d.towerPull g) eL eT
      (completedPullbackConstantIso g d) (d.derivedConstantPullbackIso g)
      (completedReductionTowerUnit d Y) (completedReductionTowerUnit d X) τ K
      (datumConstantComparison g d K) (stratumReduction_augmentation d g K)
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha
    ((completedOrdinaryPullback g d).obj K) P eP
  refine ⟨R.mapIso t ≪≫ c.symm, ?_⟩
  change completedPullbackComparison g d K ≫ (R.map t.hom ≫ c.inv) = _
  rw [← Category.assoc]
  have hu : completedPullbackComparison g d K ≫ R.map t.hom =
      intrinsicCompletionUnit X d r a ha
        ((completedOrdinaryPullback g d).obj K) P eP ≫ c.hom := by
    dsimp only [completedPullbackComparison]
    rw [Category.assoc, ← R.map_comp, ht, constantRlimUnit_eq]
    exact hc.symm
  rw [hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]

namespace ImmersionCompletedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : Y ⟶ X)

attribute [local irreducible] pbcIntegralDatum

private theorem strict_completion (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    ∃ α : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj K ≅
        wfCompletionObj Y (pbcIntegralDatum l E) r a ha
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫ α.hom =
        wfCompletionUnit Y (pbcIntegralDatum l E) r a ha
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) := by
  obtain ⟨α, hα⟩ := completion_general f (pbcIntegralDatum l E) r a ha K
    (wfCompletionRepresentative Y (pbcIntegralDatum l E)
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))
    (DerivedCategory.Q.objObjPreimageIso
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))
  refine ⟨α, ?_⟩
  simpa only [pbcActualStrictCompletedPullUnit, completedPullbackComparison,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc, Functor.map_comp, wfCompletionUnit, wfCompletionObj] using hα

end ImmersionCompletedPullback

end AlgebraicGeometry.Scheme

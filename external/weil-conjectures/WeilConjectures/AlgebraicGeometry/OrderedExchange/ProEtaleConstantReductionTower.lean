/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import WeilConjectures.AlgebraicGeometry.OrderedExchange.ConstantPerfectQuotientProjection
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Perfect projection for strict constant-coefficient reduction towers

## References

* Stacks 0A07, 099N
* Stacks Project, Tags 099M, 099N, 0E48, 0941, 0B56 and 0944
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

attribute [local irreducible] projection

private theorem isIso_of_evaluations {T : Scheme.{t}} {K L : TD (A := A) T}
    (a : K ⟶ L) (h : ∀ n : ℕᵒᵖ, IsIso ((quotientEvaluation (A := A) T n).map a)) : IsIso a := by
  rw [DerivedCategory.isIso_iff]
  intro q
  let : ∀ n : ℕᵒᵖ,
      IsIso (((DerivedCategory.homologyFunctor _ q).map a).app n) := fun n ↦ by
    have := h n
    let E := (CategoryTheory.evaluation ℕᵒᵖ
      (reductionModules T (exchangeConstantRing T A))).obj n
    exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso q) a).2
      (show IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((quotientEvaluation T n).map a)) from inferInstance)
  exact NatIso.isIso_of_isIso_app _

private theorem projection_evaluation (K : D (A := A) U) (n : ℕᵒᵖ) :
    (quotientEvaluation V n).map (projection d f K) ≫
        (quotientEvaluationPush (A := A) f n).app ((reduction d U).obj K) =
      (quotientProjection d f n).app K := by
  let a := proEtaleRingDerivedAdjunction f
    (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A)
  let b := exchangeTowerAdjunction f
    (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A)
  let α := TwoSquare.mk _ _ _ _ (reductionPullIso d f).hom
  let β := TwoSquare.mk _ _ _ _
    (quotientEvaluationPull (A := A) f n).inv
  have h := congrArg (fun z ↦ z.app K) (mateEquiv_vcomp a b a α β)
  have hp : (mateEquiv a b α).app K = projection d f K := by
    unfold projection
    exact (b.homEquiv _ _).symm_apply_eq.mp (mateEquiv_counit a b α K)
  have he : mateEquiv b a β = quotientEvaluationPush (A := A) f n := by
    rfl
  have hab : α.hComp β =
      TwoSquare.mk _ _ _ _ (quotientTensorPull d f n).hom := by
    rfl
  rw [hab] at h
  simp only [TwoSquare.vComp, TwoSquare.mk,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id] at h
  change (quotientProjection d f n).app K =
    (quotientEvaluation V n).map ((mateEquiv a b α).app K) ≫
      (mateEquiv b a β).app ((reduction d U).obj K) at h
  rw [hp, he] at h
  exact h.symm

/-- Perfect quotients make the strict projection invertible, on all ambient inputs. -/
@[instance]
theorem projection_isIso (K : D (A := A) U) : IsIso (projection d f K) := by
  apply isIso_of_evaluations
  intro n
  have : IsIso (quotientEvaluationPush (A := A) f n) :=
    AlgebraicGeometry.ProEtale.StrictTower.evalR_isIso A f n.unop
  have hf : IsIso ((quotientProjection d f n).app K) :=
    quotientProjection_isIso d f n K
  have hc : IsIso ((quotientEvaluation V n).map (projection d f K) ≫
      (quotientEvaluationPush (A := A) f n).app ((reduction d U).obj K)) := by
    rw [projection_evaluation]
    exact hf
  exact (isIso_comp_right_iff _ _).mp hc

/-- The identity comparison of ordinary constant diagrams and termwise pullback. -/
def ordinaryDiagonalPullIso :
    (Functor.const ℕᵒᵖ) ⋙ exchangeTowerModulePull f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ (Functor.const ℕᵒᵖ) :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp))
    (fun _ ↦ by ext n; simp)

/-- Exact descent of the identity comparison, retaining the derived units and counits. -/
def diagonalPullIso :
    diagonal (A := A) V ⋙ exchangeConstantPull (A := A) f ≅
      pull (A := A) f ⋙ diagonal (A := A) U :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryDiagonalPullIso (A := A) f) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

attribute [local irreducible] diagonalPullIso

/-- The direct-image/limit comparison is the adjunction conjugate of the identity square.
It is the same K-injective comparison used by comparisonT in the generic interface. -/
def directLimitIso :
    rlim (A := A) U ⋙ push (A := A) f ≅
      exchangeConstantPush (A := A) f ⋙ rlim (A := A) V :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)).comp (diagonalAdjunction (A := A) U))
    ((diagonalAdjunction (A := A) V).comp
      (exchangeTowerAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A))) (diagonalPullIso (A := A) f)

attribute [local irreducible] directLimitIso

/-- The prescribed reconstruction of constant-coefficient completed pullback. -/
def reconstruction (K : D (A := A) V) :
    (completePull d f).obj K ≅
      (rlim (A := A) U).obj ((exchangeConstantPull (A := A) f).obj ((reduction d V).obj K)) :=
  (rlim (A := A) U).mapIso ((reductionPullIso d f).symm.app K)

attribute [local irreducible] reconstruction

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The constant-coefficient H is pullback of the counit-tensor projection. -/
def H (K : D (A := A) X) :
    (reduction d Y').obj ((pull (A := A) g).obj ((push (A := A) f).obj K)) ≅
      (exchangeConstantPull (A := A) g).obj
        ((exchangeConstantPush (A := A) f).obj ((reduction d X).obj K)) :=
  (reductionPullIso d g).symm.app _ ≪≫
    (exchangeConstantPull (A := A) g).mapIso (asIso (projection d f K))

attribute [local irreducible] H

/-- Exactly the prescribed s: derived strict inverse limit of H after reconstruction. -/
def S (K : D (A := A) X) :=
  (rlim (A := A) Y').mapIso (H (f := f) (g := g) d K)

/-- Exactly the prescribed t: reconstruction followed by direct-image/limit comparison. -/
def T (K : D (A := A) X) :=
  (push (A := A) f').mapIso (reconstruction d g' K) ≪≫
    (directLimitIso (A := A) f').app
      ((exchangeConstantPull (A := A) g').obj ((reduction d X).obj K))

end AlgebraicGeometry.Scheme.OrderedExchange

namespace CategoryTheory.AdicSites.OrderedExchangeInterface

/-- The whole-diagram mate comparison is invertible on complete objects and satisfies the two
finite coefficient normalization clauses. -/
abbrev completionMateComparison
    {Y X Y' X' : Site.{u}}
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (_hperfect : PerfectQuotients A I) :
    (∀ K : X.Complete A I,
      IsIso (projectionComparison (f := f) (g := g) A I K.obj)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map (projectionComparison (f := f) (g := g) A I K.obj) ≫
          (finiteSourceIso (f := f) (g := g) A I n K.obj).hom =
        (Y'.finiteEvaluationIso A I n).hom.app ((g.pull A).obj ((f.push A).obj K.obj)) ≫
          (Y'.finiteRestriction A I n).map
            (finiteProjectionComparison (f := f) (g := g) A I n K.obj)) ∧
    (Functor.whiskerRight (completeExchange sq A I) (ObjectProperty.ι (Y'.IsComplete A I)) ≫
        (comparisonT (h := h) (k := k) A I).hom =
      comparisonS (f := f) (g := g) A I ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I)
            (towerExchange sq A)) (Y'.rlim A)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map ((towerExchange sq A).app ((X.reduction A I).obj K.obj)) ≫
          (finiteTargetIso (h := h) (k := k) A I n K.obj).hom =
        (finiteSourceIso (f := f) (g := g) A I n K.obj).hom ≫
          (Y'.finiteRestriction A I n).map
            ((ordinaryExchange sq (quotientRing A I n)).app
              ((X.finiteReduction A I n).obj K.obj))) :=
  CategoryTheory.AdicSites.completionMateComparison sq A I _hperfect

end CategoryTheory.AdicSites.OrderedExchangeInterface

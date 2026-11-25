/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
public import WeilConjectures.CategoryTheory.SixFunctors.SingleTowerEvaluationFaithful
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteIntegralProjection
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! Existence of the degree-zero tower witness for a normalized diagonal source.
Source: diagonal tower trace proof paragraph (2), evaluation and limit steps
(blueprint: lem-sfb-diagonal-trace-limit-witness-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private theorem coefficientProjection_jointly_monic
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [DiagonalTraceLocalizations l X]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) X)
    (r : Restriction l (ULift.{u} (Padic l)) X)
    (a : Coefficients l (ULift.{u} (Padic l)) X c r)
    (φ : SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)) ⟶
      SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))
    (h : ∀ n : ℕ, (diagonalCompletedRestriction l X).map φ ≫
      a.coefficientProjection.app (op n) = a.coefficientProjection.app (op n)) :
    φ = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let ev := sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ CommRingCat.{u + 1}).obj U
  apply Concrete.isLimit_ext (Scheme.purTwistZlTower X l ⋙ ev)
    (isLimitOfPreserves ev (limit.isLimit (Scheme.purTwistZlTower X l)))
  intro n
  have hn := congrArg (fun k ↦ (k.hom.app U).hom x) (h n.unop)
  change (a.coefficientProjection.app n).hom.app U ((φ.val.app U) x) =
    (a.coefficientProjection.app n).hom.app U x at hn
  exact (a.coefficient_projection n.unop U ((φ.val.app U) x)).symm.trans
    ((congrArg ((a.coefficientForget.hom.app n).hom.app U) hn).trans
      (a.coefficient_projection n.unop U x))

/-- The normalized source comparison carries the diagonal composite to one tower map.

Source: diagonal tower trace proof paragraph (2), evaluation and limit steps
(blueprint: lem-sfb-diagonal-trace-limit-witness-existence).
Proof: the completed integral is between coefficient sheaves in degree zero.
Full faithfulness writes it as a sheaf endomorphism. Its finite coefficient
projections are identities by finite diagonal integration. The actual inverse-limit
presentation of the completed coefficient sheaf detects equality of these sheaf maps,
so the integral is the identity. Use the identity on the specified degree-zero tower
and the recorded invertible unit/limit comparison to construct the required witness.
This argument uses finite detection only for ordinary sheaf maps, not arbitrary
derived morphisms. -/
theorem diagonalTrace_limitWitness_exists
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ)
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (t : Result l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f t.Rc) :
    ∃ s : SingleTowerLimitWitness (DiagonalMod l (ProjectiveLine Y))
        ((diagonalCompletedUnderlying l (ProjectiveLine Y)).map
          (a.hom ≫ t.Rc.R.map δ ≫ t.trace)),
      s.tower = t.restrictionS.F.obj
          (SpTowerClasses.coefficient (ProjectiveLine Y)
            (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (ProjectiveLine Y))) ∧
        s.limitFunctor = t.LS.R := by
  let U := diagonalCompletedRestriction l (ProjectiveLine Y)
  let g := a.hom ≫ t.Rc.R.map δ ≫ t.trace
  obtain ⟨φ, hφ⟩ :=
    (DerivedCategory.singleFunctor (DiagonalCompleted l (ProjectiveLine Y)) 0).map_surjective g
  have hlevels (n : ℕ) : U.map φ ≫ t.coefficientsS.coefficientProjection.app (op n) =
      t.coefficientsS.coefficientProjection.app (op n) := by
    apply (DerivedCategory.singleFunctor (DiagonalMod l (ProjectiveLine Y)) 0).map_injective
    apply (cancel_epi ((U.mapDerivedCategorySingleFunctor 0).hom.app _)).1
    have hnat := (U.mapDerivedCategorySingleFunctor 0).hom.naturality φ
    dsimp only [Functor.comp_map] at hnat
    rw [Functor.map_comp, ← Category.assoc, ← hnat]
    rw [hφ]
    simpa only [Category.assoc] using
      diagonalTrace_finiteIntegralProjection l Y hY D δ hδ f hf t a n
  have hφid : φ = 𝟙 _ :=
    coefficientProjection_jointly_monic l (ProjectiveLine Y) t.chernS t.restrictionS
      t.coefficientsS φ hlevels
  have hg : g = 𝟙 _ := by
    rw [← hφ, hφid, CategoryTheory.Functor.map_id]
  have : IsIso (t.coefficientsS.unitMap l (ULift.{u} (Padic l)) t.LS) := t.unit_limit
  let j := asIso (t.coefficientsS.unitMap l (ULift.{u} (Padic l)) t.LS) ≪≫
    t.LS.R.mapIso ((t.restrictionS.F.mapDerivedCategorySingleFunctor 0).app
      (SpTowerClasses.coefficient (ProjectiveLine Y)
        (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (ProjectiveLine Y))))
  refine ⟨{
    tower := t.restrictionS.F.obj
      (SpTowerClasses.coefficient (ProjectiveLine Y)
        (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (ProjectiveLine Y)))
    limitFunctor := t.LS.R
    endomorphism := 𝟙 _
    comparison := j
    evaluations := fun n ↦ CategoryTheory.Functor.map_id _ _
    square := ?_ }, rfl, rfl⟩
  change U.mapDerivedCategory.map g ≫ j.hom = _
  simp only [hg, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.ProEtale.DiagonalTrace

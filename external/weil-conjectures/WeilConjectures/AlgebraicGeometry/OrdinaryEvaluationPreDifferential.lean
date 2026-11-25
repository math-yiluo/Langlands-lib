/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly
import WeilConjectures.AlgebraicGeometry.OrdinaryDualProjectionDifferential
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationPrecompositionNaturality

/-! # Ordinary evaluation and one part of the differential

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-pre-differential).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

local instance ordinaryPreMonoidalPreadditive (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

private theorem evaluation_sign {A : Type*} [AddCommGroup A]
    (p q n : ℤ) (h : p + q = n) (x : A) :
    p.negOnePow • ((-q.negOnePow) • x) = -(n.negOnePow • x) := by
  rw [smul_smul, mul_neg, ← Int.negOnePow_add, h, Units.neg_smul]

set_option backward.isDefEq.respectTransparency.types true in
/-- The signed dual differential gives precomposition in the input complex.
Source: Stacks Project, Tag 08DQ, ordinary evaluation calculation, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-pre-differential).

Proof: Both sides vanish unless r+q=-1. Expand the dual differential after
its projection to Hom(P^r,O[0]^(r+q+1)). The postcomposition term is zero
because the single complex has zero differential. The remaining term is
-(-1)^q times precomposition by d_P. Move this term through evaluation by
naturality of the tensor-Hom equivalence in its input and its tensor source.
Additivity of currying and tensoring moves the scalar outside. The tensor
sign (-1)^p combines with (-1)^q to give (-1)^n since p+q=n. The transport
in F identifies (r+1)+n with r+m, with no choice of data. If r+q is not -1,
the projections involved have zero target, so the same identity holds with
both sides zero. Zero modules and empty opens require no separate assumption. -/
theorem ordinaryEvaluation_pre_differential (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (n m p q r : ℤ) (hnm : n + 1 = m) (hpq : p + q = n) :
    p.negOnePow • ((F.X p ◁ (localEvaluationDual X U P).d q (q + 1)) ≫
        localEvaluationComponent X U P F p (q + 1) m r (by omega)) =
      -(n.negOnePow • (localEvaluationComponent X U P F p q n (r + 1) hpq ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) (P.d r (r + 1))
          (F.XIsoOfEq (by omega : (r + 1) + n = r + m)).hom))  := by
  classical
  by_cases h : r + (q + 1) = 0
  · have hd := ordinaryEvaluation_dual_projection_differential X U P q r h
    have hc := ordinaryEvaluation_precomposition_naturality X U P F p q (q + 1)
      n m r (r + 1) hpq (by omega) h (by omega) (by omega)
      (P.d r (r + 1)) ((localEvaluationDual X U P).d q (q + 1)) (-q.negOnePow) hd
    rw [hc]
    exact evaluation_sign p q n hpq _
  · have h' : ¬ (r + 1) + q = 0 := by omega
    simp only [localEvaluationComponent, dite_eq_right h, dite_eq_right h', comp_zero,
      zero_comp, smul_zero, neg_zero]

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData

/-! # Ordinary evaluation and one part of the differential

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-dual-projection-differential).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem projectionHomMap_zero (X : Scheme.{u}) (U : X.Opens)
    {A A' B B' : localEvaluationModules X U} (f : A' ⟶ A) :
    SheafOfModules.homObjMap (R := X.sheaf.over U) f (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  ext V φ : 3
  change (PresheafOfModules.restrictOver (X.sheaf.over U).obj V.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver (X.sheaf.over U).obj V.unop).map 0 = 0
  ext W x
  rfl

/-- The dual differential after its degree-zero projection.
Source: Stacks Project, Tag 0A8X, section-hom-complexes, differential formula.
(blueprint: lem-pc-ordinary-dual-projection-differential).
Proof: apply the differential clause of homComplex_projections_exists to
P and the structure sheaf in degree zero, with output indices r+q and 0,
and input indices r and r+1. The single complex has zero differential, so
its postcomposition term vanishes. The remaining term is precomposition
by d_P with coefficient -(-1)^q. This uses no finiteness or nonzero condition. -/
theorem ordinaryEvaluation_dual_projection_differential (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ)
    (q r : ℤ) (h : r + (q + 1) = 0) :
    (localEvaluationDual X U P).d q (q + 1) ≫
        localEvaluationProjection X U P (localEvaluationUnit X U) (q + 1) r 0 h =
      (-q.negOnePow) •
        (localEvaluationProjection X U P (localEvaluationUnit X U) q (r + 1) 0
          (by omega) ≫ SheafOfModules.homObjMap (R := X.sheaf.over U)
            (P.d r (r + 1)) (𝟙 ((localEvaluationUnit X U).X 0)))  := by
  classical
  have hd := (Classical.choose_spec
    (homComplex_projections_exists (R := X.sheaf.over U))).2.1
      P (localEvaluationUnit X U) q (q + 1) r 0 (r + q) (r + 1)
      rfl h rfl (by omega)
  change (localEvaluationDual X U P).d q (q + 1) ≫
    localEvaluationProjection X U P (localEvaluationUnit X U) (q + 1) r 0 h = _ at hd
  rw [hd]
  simp only [localEvaluationProjection, localEvaluationUnit, HomologicalComplex.single_obj_d,
    projectionHomMap_zero, comp_zero, zero_sub, Units.neg_smul]


end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationPostDifferential
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationPreDifferential
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-! # The ordinary evaluation differential on one tensor summand

Source: Stacks Project, Tag 08DQ, and Section 20.41.
(blueprint: lem-pc-ordinary-evaluation-differential-summand).
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

attribute [local instance] ordinaryPostMonoidalPreadditive

private theorem projection_transport (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (n r s : ℤ) (h : r + n = s) :
    localEvaluationProjection X U P F n r s h =
      localEvaluationProjection X U P F n r (r + n) rfl ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r)) (F.XIsoOfEq h).hom := by
  subst s
  simp

set_option backward.isDefEq.respectTransparency true in
/-- On a single tensor summand, evaluation satisfies the projected differential equation.
Source: Stacks Project, Tag 08DQ, ordinary complex comparison; Section 20.41,
Hom-complex differential.
(blueprint: lem-pc-ordinary-evaluation-differential-summand).

Proof: Use the specified component formula for the graded maps e. On the summand
F^p tensor D^q, the total differential is d_F tensor 1 plus (-1)^p times
1 tensor d_D. Expand the differential of Hom(P,F) after its rth projection:
postcomposition with d_F minus (-1)^n precomposition with d_P. For r+q=0,
only the d_F terms remain; evaluation and the right unit action are natural
in F, so these terms agree. For r+q=-1, only the d_P terms remain. Expand
the Hom differential of D=Hom(P,O[0]); the differential of O[0] vanishes,
so it is -(-1)^q times precomposition with d_P. Naturality in P identifies
these contributions and (-1)^p (-1)^q=(-1)^(p+q)=(-1)^n gives the sign.
For every other r+q, both component formulas are zero. The degree transports
agree by proof irrelevance. These arguments apply to zero terms and empty
opens; no boundedness or perfectness is used. This is only a calculation on
one summand and one projection, without assembling the global equation. -/
theorem ordinaryEvaluation_differential_summand (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (e : ∀ n : ℤ, (localEvaluationTensor X U P F).X n ⟶
      (homComplex (R := X.sheaf.over U) P F).X n)
    (he : ∀ (p q n r : ℤ) (h : p + q = n),
      HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
          (curriedTensor _) (.up ℤ) p q n h ≫ e n ≫
        localEvaluationProjection X U P F n r (r + n) rfl =
          localEvaluationComponent X U P F p q n r h)
    (n m p q r : ℤ) (hnm : (ComplexShape.up ℤ).Rel n m) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n hpq ≫ e n ≫
      (homComplex (R := X.sheaf.over U) P F).d n m ≫
      localEvaluationProjection X U P F m r (r + m) rfl =
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n hpq ≫
      (localEvaluationTensor X U P F).d n m ≫ e m ≫
      localEvaluationProjection X U P F m r (r + m) rfl := by
  have hnm' : n + 1 = m := hnm
  have hd : (homComplex (R := X.sheaf.over U) P F).d n m ≫
      localEvaluationProjection X U P F m r (r + m) rfl =
    localEvaluationProjection X U P F n r (r + n) rfl ≫
      SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
        (F.d (r + n) (r + m)) -
    n.negOnePow • (localEvaluationProjection X U P F n (r + 1) (r + m) (by omega) ≫
      SheafOfModules.homObjMap (R := X.sheaf.over U) (P.d r (r + 1))
        (𝟙 (F.X (r + m)))) := by
    exact (Classical.choose_spec
      (homComplex_projections_exists (R := X.sheaf.over U))).2.1
        P F n m r (r + m) (r + n) (r + 1) hnm' rfl rfl (by omega)
  conv_lhs =>
    arg 2
    arg 2
    rw [hd]
  simp only [Preadditive.comp_sub, Linear.comp_units_smul]
  simp only [← Category.assoc] at he ⊢
  simp only [he]
  simp only [projection_transport X U P F n (r + 1) (r + m) (by omega)]
  simp only [← Category.assoc] at he ⊢
  simp only [he]
  simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
    Category.comp_id]
  simp only [ordinaryEvaluation_post_differential X U P F n m p q r hnm' hpq]
  change _ = HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
      (curriedTensor _) (.up ℤ) p q n hpq ≫
    (HomologicalComplex.mapBifunctor F (localEvaluationDual X U P)
      (curriedTensor _) (.up ℤ)).d n m ≫ e m ≫
      localEvaluationProjection X U P F m r (r + m) rfl
  conv_rhs =>
    arg 2
    arg 1
    rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp, ← Category.assoc]
  simp only [HomologicalComplex.mapBifunctor.ι_D₁ F (localEvaluationDual X U P)
      (curriedTensor _) (.up ℤ),
    HomologicalComplex.mapBifunctor.ι_D₂ F (localEvaluationDual X U P)
      (curriedTensor _) (.up ℤ)]
  have hfirst := HomologicalComplex.mapBifunctor.d₁_eq F
    (localEvaluationDual X U P) (curriedTensor (localEvaluationModules X U)) (.up ℤ)
    (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q m
      (by change p + 1 + q = m; omega)
  have hsecond := HomologicalComplex.mapBifunctor.d₂_eq F
    (localEvaluationDual X U P) (curriedTensor (localEvaluationModules X U)) (.up ℤ)
    p (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) m
      (by change p + (q + 1) = m; omega)
  simp only [hfirst, hsecond]
  simp only [show ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = 1 from rfl,
    show ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = p.negOnePow from rfl,
    one_smul, Linear.units_smul_comp, Category.assoc,
    curriedTensor_obj_map, curriedTensor_map_app]
  simp only [← Category.assoc, he]
  simp only [ordinaryEvaluation_pre_differential X U P F n m p q r hnm' hpq,
    sub_eq_add_neg]

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicTopology.SetCechNerveFreeResolution

/-!
# Exactness of the free module presheaf nerve

Source: Stacks Project, Cohomology on Sites, Tags 03F5, 03AT; Hypercoverings, 01GC.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The alternating chain complex of free module presheaves on the Čech nerve.
Source: Stacks Project, Tags 03AS and 01GC.
(blueprint: lem-sc-presheaf-free-nerve-exact) -/
noncomputable def presheafFreeNerveComplex
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) : ChainComplex (PresheafOfModules.{v} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ PresheafOfModules.free R)

/-- Objectwise exactness of a complex of presheaf modules implies exactness.
Source: Mathlib categorical exactness of jointly conservative evaluations.
(blueprint: lem-sc-presheaf-free-nerve-exact-eval-glue)
Proof: kernels and cokernels in presheaf module categories are computed objectwise,
so the family of evaluation functors jointly reflects the zero homology condition. -/
theorem exactAt_of_presheaf_evaluations
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (K : ChainComplex (PresheafOfModules.{v} R) ℕ) (a : ℕ)
    (h : ∀ X : Cᵒᵖ, (((PresheafOfModules.evaluation R X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).ExactAt a) : K.ExactAt a := by
  have hf : JointlyFaithful (fun X ↦ PresheafOfModules.evaluation R X) :=
    ⟨fun hfg ↦ by
      ext X x
      exact congrArg (fun k ↦ k.hom x) (hfg X)⟩
  exact (hf.jointlyReflectsIsomorphisms.exactAt_iff K a).2 h

private def nerveRangeEquiv {A B : Type v} (f : A → B) (n : ℕ) :
    AlgebraicTopology.setCechNerve f n ≃
      AlgebraicTopology.setCechNerve (Set.rangeFactorization f) n where
  toFun x := ⟨x.1, fun i ↦ Subtype.ext (x.2 i)⟩
  invFun x := ⟨x.1, fun i ↦ congrArg Subtype.val (x.2 i)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def nerveRangeLinearEquiv {A B : Type v}
    (S : Type v) [Ring S] (f : A → B) (n : ℕ) :
    AlgebraicTopology.setCechNerveModule S f n ≃ₗ[S]
      AlgebraicTopology.setCechNerveModule S (Set.rangeFactorization f) n :=
  Finsupp.domLCongr (nerveRangeEquiv f n)

private theorem nerveRangeLinearEquiv_d {A B : Type v}
    (S : Type v) [Ring S] (f : A → B) (n : ℕ) :
    (AlgebraicTopology.setCechDifferential S (Set.rangeFactorization f) n).comp
        (nerveRangeLinearEquiv S f (n + 1)).toLinearMap =
      (nerveRangeLinearEquiv S f n).toLinearMap.comp
        (AlgebraicTopology.setCechDifferential S f n) := by
  classical
  apply Finsupp.lhom_ext
  intro x r
  simp [AlgebraicTopology.setCechDifferential, nerveRangeLinearEquiv,
    AlgebraicTopology.setCechFace, nerveRangeEquiv]

private theorem setNerve_positive_exact {A B : Type v}
    (S : Type v) [Ring S] (f : A → B) (n : ℕ) :
    LinearMap.range (AlgebraicTopology.setCechDifferential S f (n + 1)) =
      LinearMap.ker (AlgebraicTopology.setCechDifferential S f n) := by
  have hex := (AlgebraicTopology.setCechNerve_free_resolution S
    (Set.rangeFactorization f) Set.rangeFactorization_surjective).2.2.2.2 n
  have ht := Function.Exact.iff_of_ladder_linearEquiv
    (nerveRangeLinearEquiv_d S f (n + 1)) (nerveRangeLinearEquiv_d S f n)
  simpa only [LinearMap.exact_iff, eq_comm] using ht.mp
    (by simpa only [LinearMap.exact_iff, eq_comm] using hex)

set_option backward.isDefEq.respectTransparency.types false in
private def nerveSectionsEquiv {C : Type u} [Category.{v} C]
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (X : Cᵒᵖ) (n : ℕ) :
    ((WidePullbackShape.wideCospan f.right (fun _ : Fin (n + 1) ↦ f.left)
      (fun _ ↦ f.hom)) ⋙ (evaluation Cᵒᵖ (Type v)).obj X).sections ≃
      AlgebraicTopology.setCechNerve (f.hom.app X) n where
  toFun s := ⟨fun i ↦ s.1 (some i), by
    intro i
    have hi : f.hom.app X (s.1 (some i)) = s.1 none := by
      simpa [WidePullbackShape.wideCospan] using s.2 (WidePullbackShape.Hom.term i)
    have h0 : f.hom.app X (s.1 (some 0)) = s.1 none := by
      simpa [WidePullbackShape.wideCospan] using s.2 (WidePullbackShape.Hom.term 0)
    exact hi.trans h0.symm⟩
  invFun x := ⟨fun j ↦ match j with
    | none => f.hom.app X (x.1 0)
    | some i => x.1 i, by
      intro i j g
      cases g with
      | id j => rfl
      | term i => exact x.2 i⟩
  left_inv s := by
    apply Subtype.ext
    funext j
    cases j with
    | none => exact s.2 (WidePullbackShape.Hom.term 0)
    | some i => rfl
  right_inv _ := rfl

private noncomputable def evaluatedNerveEquiv {C : Type u} [Category.{v} C]
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (X : Cᵒᵖ) (n : ℕ) :
    (f.cechNerve.obj (Opposite.op (SimplexCategory.mk n))).obj X ≃
      AlgebraicTopology.setCechNerve (f.hom.app X) n :=
  (Types.isLimitEquivSections (isLimitOfPreserves
    ((evaluation Cᵒᵖ (Type v)).obj X)
    (limit.isLimit (WidePullbackShape.wideCospan f.right
      (fun _ : Fin (n + 1) ↦ f.left) (fun _ ↦ f.hom))))).trans
    (nerveSectionsEquiv f X n)

private theorem evaluatedNerveEquiv_face {C : Type u} [Category.{v} C]
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (X : Cᵒᵖ) (n : ℕ) (j : Fin (n + 2))
    (x : (f.cechNerve.obj (Opposite.op (SimplexCategory.mk (n + 1)))).obj X) :
    evaluatedNerveEquiv f X n ((f.cechNerve.δ j).app X x) =
      AlgebraicTopology.setCechFace (f.hom.app X) j
        (evaluatedNerveEquiv f X (n + 1) x) := by
  apply Subtype.ext
  funext i
  change (WidePullback.π (fun _ : Fin (n + 1) ↦ f.hom) i).app X
      ((f.cechNerve.δ j).app X x) =
    (WidePullback.π (fun _ : Fin (n + 2) ↦ f.hom) (j.succAbove i)).app X x
  have h := WidePullback.lift_π (fun _ : Fin (n + 1) ↦ f.hom)
    (WidePullback.base (fun _ : Fin (n + 2) ↦ f.hom))
    (fun k ↦ WidePullback.π (fun _ : Fin (n + 2) ↦ f.hom)
      ((SimplexCategory.δ j).toOrderHom k)) (by simp) i
  exact congrArg (fun k ↦ k.app X x) h

private noncomputable def evaluatedNerveLinearEquiv
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (X : Cᵒᵖ) (n : ℕ) :
    ((f.cechNerve.obj (Opposite.op (SimplexCategory.mk n))).obj X →₀ R.obj X) ≃ₗ[R.obj X]
      AlgebraicTopology.setCechNerveModule (R.obj X) (f.hom.app X) n :=
  Finsupp.domLCongr (evaluatedNerveEquiv f X n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem evaluatedNerveLinearEquiv_d
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (X : Cᵒᵖ) (n : ℕ) :
    (AlgebraicTopology.setCechDifferential (R.obj X) (f.hom.app X) n).comp
        (evaluatedNerveLinearEquiv R f X (n + 1)).toLinearMap =
      (evaluatedNerveLinearEquiv R f X n).toLinearMap.comp
        ((((PresheafOfModules.evaluation R X).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (presheafFreeNerveComplex R f)).d (n + 1) n).hom := by
  classical
  simp only [Functor.mapHomologicalComplex_obj_d, presheafFreeNerveComplex,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  change (AlgebraicTopology.setCechDifferential (R.obj X) (f.hom.app X) n).comp
      (evaluatedNerveLinearEquiv R f X (n + 1)).toLinearMap =
    (evaluatedNerveLinearEquiv R f X n).toLinearMap.comp
      ((PresheafOfModules.evaluation R X).map
        (AlgebraicTopology.AlternatingFaceMapComplex.objD
          (f.cechNerve ⋙ PresheafOfModules.free R) n)).hom
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD,
    Functor.map_sum, Functor.map_zsmul, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  apply Finsupp.lhom_ext
  intro x r
  simp only [Arrow.cechNerve_obj, AlgebraicTopology.setCechDifferential,
    Finsupp.smul_single, smul_eq_mul, mul_one, evaluatedNerveLinearEquiv,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, Finsupp.equivMapDomain_single, Finsupp.lift_apply,
    Finset.smul_sum, zero_mul, Finsupp.single_zero, Finset.sum_const_zero,
    Finsupp.sum_single_index, PresheafOfModules.evaluation, PresheafOfModules.free,
    ModuleCat.free, Functor.comp_obj, PresheafOfModules.freeObj_obj, Int.reduceNeg,
    SimplicialObject.δ, Functor.comp_map, Arrow.cechNerve_map, Quiver.Hom.unop_op,
    ConcreteCategory.hom_ofHom, LinearMap.coe_sum, LinearMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change Finsupp.single
      (AlgebraicTopology.setCechFace (f.hom.app X) j
        (evaluatedNerveEquiv f X (n + 1) x)) (r * (-1) ^ (j : ℕ)) =
    Finsupp.single (evaluatedNerveEquiv f X n ((f.cechNerve.δ j).app X x))
      ((-1) ^ (j : ℕ) * r)
  rw [evaluatedNerveEquiv_face]
  congr 1
  exact ((Commute.neg_one_left r).pow_left (j : ℕ)).eq.symm

/-- Objectwise exactness of the evaluated free nerve.
Source: Stacks Project, Tags 03F5 and 03AT.
The evaluated complex is identified with the set Cech free resolution.
(blueprint: lem-sc-presheaf-free-nerve-exact-eval)
-/
theorem presheafFreeNerveComplex_exactAt_eval
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (n : ℕ) (X : Cᵒᵖ) :
    (((PresheafOfModules.evaluation R X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (presheafFreeNerveComplex R f)).ExactAt (n + 1) := by
  let K := (((PresheafOfModules.evaluation R X).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (presheafFreeNerveComplex R f))
  change K.ExactAt (n + 1)
  rw [K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (K.d (n + 2) (n + 1)).hom =
    LinearMap.ker (K.d (n + 1) n).hom
  have ht := Function.Exact.iff_of_ladder_linearEquiv
    (evaluatedNerveLinearEquiv_d R f X (n + 1))
    (evaluatedNerveLinearEquiv_d R f X n)
  simpa only [LinearMap.exact_iff, eq_comm] using ht.mp
    (by simpa only [LinearMap.exact_iff, eq_comm] using
      setNerve_positive_exact (R.obj X) (f.hom.app X) n)

/-- (blueprint: lem-sc-presheaf-free-nerve-exact) -/
theorem presheafFreeNerveComplex_exactAt
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (n : ℕ) :
    (presheafFreeNerveComplex R f).ExactAt (n + 1) := by
  apply exactAt_of_presheaf_evaluations R
  exact presheafFreeNerveComplex_exactAt_eval R f n

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Localized Hom-complex cycles

Source: Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y.
This module states the lifting of localized chain maps to cycles.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true in
/-- A localized chain map lifts to a sectionwise degree-zero cycle.
Source: Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y.
(blueprint: lem-pur-localized-hom-complex-cycle-lift)

Proof: evaluation at U preserves the degree-zero product cone in homComplex_exists.
Each component of g is an internal-Hom section over U, so this product cone supplies
an element x of the evaluated degree-zero term with those projections. Compose the
differential of x with each degree-one projection. The differential formula at n = 0
is postcomposition by d_I minus precomposition by d_L. The chain-map identity of g
makes this difference zero on every slice object. Evaluation also preserves the
degree-one product, whose projections jointly detect zero, so d x = 0. The kernel
universal property of the cycle inclusion supplies z mapping to x. Its projections
are the prescribed components. This uses all integer degrees without boundedness. -/
theorem localizedHomComplex_cycle_lift
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ g : (res.obj L ⟶ res.obj I), ∃ z : S.cycles 0,
      ∀ (p : ℤ) (W : (Over U)ᵒᵖ),
        (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W =
          (g.f p).val.app W := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
  let H := homComplex (R := R) L I
  let π := Classical.choose (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
  let E := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
    forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat
  let S := (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj H
  let := hzero
  let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  change ∀ g : res.obj L ⟶ res.obj I, _
  intro g
  let T := E ⋙ forget AddCommGrpCat
  let c (n : ℤ) := Limits.Fan.mk (H.X n) (fun p : ℤ ↦ π L I n p (p + n) rfl)
  have hc (n : ℤ) : Limits.IsLimit (c n) :=
    (Classical.choose_spec (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))).1 L I n
      |>.some
  let e (n : ℤ) := Limits.Types.isLimitEquivSections (Limits.isLimitOfPreserves T (hc n))
  let a (p : ℤ) : T.obj (SheafOfModules.homObj (R := R) (L.X p) (I.X p)) :=
    { app W := ModuleCat.ofHom
        { toFun := (g.f p).val.app W
          map_add' := map_add _
          map_smul' := fun r x ↦ by exact ((g.f p).val.app W).hom.map_smul r x }
      naturality := fun f ↦ by
        ext x
        exact PresheafOfModules.naturality_apply (g.f p).val f x }
  have hx : ∃ x : S.X 0, ∀ p : ℤ,
      ((π L I 0 p p (add_zero p)).val.app (op U)) x = a p := by
    let b : (Discrete.functor (fun p : ℤ ↦
        SheafOfModules.homObj (R := R) (L.X p) (I.X (p + 0))) ⋙ T).sections :=
      ⟨fun j ↦ by
        change T.obj (SheafOfModules.homObj (R := R) (L.X j.as) (I.X (j.as + 0)))
        simpa only [add_zero] using a j.as, by
        intro ⟨i⟩ ⟨j⟩ f
        obtain rfl := Discrete.eq_of_hom f
        simp⟩
    refine ⟨(e 0).symm b, ?_⟩
    intro p
    have h := Limits.Types.isLimitEquivSections_symm_apply
      (Limits.isLimitOfPreserves T (hc 0)) b (Discrete.mk p)
    cases p <;> exact h
  obtain ⟨x, hx⟩ := hx
  have hd : S.d 0 1 x = 0 := by
    apply Limits.Concrete.isLimit_ext _ (Limits.isLimitOfPreserves E (hc 1))
    intro ⟨p⟩
    change ((π L I 1 p (p + 1) rfl).val.app (op U)) (S.d 0 1 x) =
      ((π L I 1 p (p + 1) rfl).val.app (op U)) 0
    refine Eq.trans ?_ (((π L I 1 p (p + 1) rfl).val.app (op U)).hom.map_zero.symm)
    have hd := (Classical.choose_spec (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))).2.1
      L I 0 1 p (p + 1) p (p + 1) rfl rfl (add_zero p) (add_zero (p + 1))
    have he := congrArg
      (fun k : H.X 0 ⟶ SheafOfModules.homObj (R := R) (L.X p) (I.X (p + 1)) ↦
        (k.val.app (op U)) x) hd
    simp only [Int.negOnePow_zero, one_smul] at he
    change ((π L I 1 p (p + 1) rfl).val.app (op U)) (S.d 0 1 x) =
      (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (I.d p (p + 1))).val.app (op U)
        (((π L I 0 p p (add_zero p)).val.app (op U)) x) -
      (SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (I.X (p + 1)))).val.app
        (op U) (((π L I 0 (p + 1) (p + 1) (add_zero (p + 1))).val.app (op U)) x) at he
    refine he.trans ?_
    apply sub_eq_zero.mpr
    have h₁ := congrArg
      (fun y ↦ (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p))
        (I.d p (p + 1))).val.app (op U) y) (hx p)
    have h₂ := congrArg
      (fun y ↦ (SheafOfModules.homObjMap (R := R) (L.d p (p + 1))
        (𝟙 (I.X (p + 1)))).val.app (op U) y) (hx (p + 1))
    refine h₁.trans (Eq.trans ?_ h₂.symm)
    change (PresheafOfModules.restrictOver R.obj U).map (𝟙 (L.X p).val) ≫
      a p ≫ (PresheafOfModules.restrictOver R.obj U).map (I.d p (p + 1)).val =
      (PresheafOfModules.restrictOver R.obj U).map (L.d p (p + 1)).val ≫
        a (p + 1) ≫
          (PresheafOfModules.restrictOver R.obj U).map (𝟙 (I.X (p + 1)).val)
    apply PresheafOfModules.hom_ext
    intro W
    ext t
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app W) (g.comm p (p + 1))) t
  have hk : x ∈ (S.sc 0).g.hom.ker := by
    change S.d 0 ((ComplexShape.up ℤ).next 0) x = 0
    rw [CochainComplex.next ℤ (0 : ℤ)]
    exact hd
  refine ⟨(S.sc 0).abCyclesIso.inv ⟨x, hk⟩, ?_⟩
  intro p W
  have hz := (S.sc 0).abCyclesIso_inv_apply_iCycles ⟨x, hk⟩
  change S.iCycles 0 ((S.sc 0).abCyclesIso.inv ⟨x, hk⟩) = x at hz
  change (((π L I 0 p p (add_zero p)).val.app (op U))
    (S.iCycles 0 ((S.sc 0).abCyclesIso.inv ⟨x, hk⟩))).app W = (g.f p).val.app W
  -- Transport the section equalities without rewriting the dependent projection types.
  exact congrArg (fun y ↦ y.app W)
    ((congrArg ((π L I 0 p p (add_zero p)).val.app (op U)) hz).trans (hx p))

end CategoryTheory

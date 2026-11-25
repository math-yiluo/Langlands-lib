/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Int.Interval

/-! # Finite target decomposition

Source: Stacks Project, Tags 08DQ and 08DM.
(blueprint: lem-pc-ordinary-evaluation-target-biproduct).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] localEvaluationPreadditive

private theorem homObj_isZero_left (X : Scheme.{u}) (U : X.Opens)
    (A B : localEvaluationModules X U) (hA : IsZero A) :
    IsZero (SheafOfModules.homObj (R := X.sheaf.over U) A B) := by
  rw [IsZero.iff_id_eq_zero,
    ← SheafOfModules.homObjMap_id (R := X.sheaf.over U) (M := A) (N := B),
    (IsZero.iff_id_eq_zero A).mp hA]
  apply SheafOfModules.hom_ext
  ext V φ : 3
  change (PresheafOfModules.restrictOver _ V.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver _ V.unop).map (𝟙 B.val) = 0
  ext W x
  change (φ.app W).hom (0) = 0
  exact map_zero _

/-- The ordinary Hom degree is the finite biproduct of its supported factors.
Source: Stacks Project, Tag 08DM, proof of `lemma-Rhom-strictly-perfect`,
finite product versus sum, and Tag 08DQ, Hom sum.
(blueprint: lem-pc-ordinary-evaluation-target-biproduct).

Proof: homComplex_projections_exists exhibits the displayed projections as a
product over all integers r. For r outside [a,b], P^r is zero, so internal Hom
from P^r to F^(r+n) is zero. A map into any such factor is unique. Thus the
restricted finite fan is still limiting: extend any cone by the unique zero
maps, lift to the original product, and use its projection extensionality for
uniqueness. Finite products in this additive category are biproducts. The
unique limit comparison is an isomorphism and satisfies the projection equations.
The same construction works for an empty interval and for zero F or empty U. -/
theorem ordinaryEvaluation_target_biproduct (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) (a b n : ℤ)
    (hbounded : ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r)) :
    ∃ e : (homComplex (R := X.sheaf.over U) P F).X n ≅
        (⨁ fun r : ↥(Finset.Icc a b) ↦
          SheafOfModules.homObj (R := X.sheaf.over U) (P.X r.val) (F.X (r.val + n))),
      ∀ r : ↥(Finset.Icc a b),
        e.hom ≫ biproduct.π _ r =
          localEvaluationProjection X U P F n r.val (r.val + n) rfl := by
  classical
  let T : ↥(Finset.Icc a b) → localEvaluationModules X U := fun r ↦
    SheafOfModules.homObj (R := X.sheaf.over U) (P.X r.val) (F.X (r.val + n))
  let H := (homComplex (R := X.sheaf.over U) P F).X n
  let π : ∀ r : ℤ, H ⟶
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X (r + n)) :=
    fun r ↦ localEvaluationProjection X U P F n r (r + n) rfl
  have hlim : IsLimit (Fan.mk H π) :=
    Classical.choice ((Classical.choose_spec
      (homComplex_projections_exists (R := X.sheaf.over U))).1 P F n)
  let f : H ⟶ ⨁ T := biproduct.lift fun r ↦ π r.val
  let cone : Fan (fun r : ℤ ↦
      SheafOfModules.homObj (R := X.sheaf.over U) (P.X r) (F.X (r + n))) :=
    Fan.mk (⨁ T) fun r ↦ if hr : r ∈ Finset.Icc a b then biproduct.π T ⟨r, hr⟩ else 0
  let g : (⨁ T) ⟶ H := hlim.lift cone
  have hg (r : ℤ) : g ≫ π r =
      if hr : r ∈ Finset.Icc a b then biproduct.π T ⟨r, hr⟩ else 0 :=
    hlim.fac cone (Discrete.mk r)
  have hfg : f ≫ g = 𝟙 H := by
    apply hlim.hom_ext
    intro j
    rcases j with ⟨r⟩
    change (f ≫ g) ≫ π r = 𝟙 H ≫ π r
    rw [Category.assoc, hg]
    by_cases hr : r ∈ Finset.Icc a b
    · simp [hr, f]
    · have hz : IsZero (SheafOfModules.homObj (R := X.sheaf.over U)
          (P.X r) (F.X (r + n))) := by
        apply homObj_isZero_left X U _ _
        apply hbounded r
        simp only [Finset.mem_Icc, not_and_or, not_le] at hr
        exact hr
      exact hz.eq_of_tgt _ _
  have hgf : g ≫ f = 𝟙 (⨁ T) := by
    apply biproduct.hom_ext
    intro r
    simp only [Category.assoc, f, biproduct.lift_π, Category.id_comp]
    rw [hg]
    simp
  refine ⟨⟨f, g, hfg, hgf⟩, ?_⟩
  intro r
  exact biproduct.lift_π _ r

end AlgebraicGeometry

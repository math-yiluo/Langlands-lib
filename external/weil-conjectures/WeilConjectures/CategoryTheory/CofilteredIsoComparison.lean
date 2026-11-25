/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.Category

/-! # Comparison of an invertible diagram over a cofiltered category

Source: common-refinement cancellation in lem-fix-weil-operations.proof.md,
paragraph 1 (blueprint: lem-pod-cofiltered-iso-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w z
open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [IsCofilteredOrEmpty C]
  {B : Type w} [Category.{z} B] (F : Cᵒᵖ ⥤ B)
  (hF : ∀ {i j : C} (f : i ⟶ j), IsIso (F.map f.op))

/-- Compare through the specified cofiltered cone, using only inverse diagram arrows.
Source: common refinements (blueprint: lem-pod-cofiltered-iso-comparison). -/
def cofilteredIsoComparison (i j : C) : F.obj (op i) ≅ F.obj (op j) :=
  @asIso _ _ _ _ (F.map (IsCofiltered.minToLeft i j).op) (hF _) ≪≫
    (@asIso _ _ _ _ (F.map (IsCofiltered.minToRight i j).op) (hF _)).symm

/-- Every cone gives the same comparison, characterized by cancellation.
Source: common-refinement independence (blueprint: lem-pod-cofiltered-iso-comparison).
Proof: refine the two cones by a bowtie. Apply the diagram to its two equalities,
cancel the second chosen cone arrow and then cancel the arrow of the common refinement. -/
theorem cofilteredIsoComparison_normalized {i j d : C} (u : d ⟶ i) (v : d ⟶ j) :
    (cofilteredIsoComparison F hF i j).hom ≫ F.map v.op = F.map u.op := by
  let u₀ := IsCofiltered.minToLeft i j
  let v₀ := IsCofiltered.minToRight i j
  obtain ⟨s, a, b, hi, hj⟩ := IsCofiltered.bowtie u₀ u v₀ v
  have hi' : F.map u₀.op ≫ F.map a.op = F.map u.op ≫ F.map b.op := by
    simpa only [op_comp, Functor.map_comp] using
      congrArg (fun t : s ⟶ i ↦ F.map t.op) hi
  have hj' : F.map v₀.op ≫ F.map a.op = F.map v.op ≫ F.map b.op := by
    simpa only [op_comp, Functor.map_comp] using
      congrArg (fun t : s ⟶ j ↦ F.map t.op) hj
  have := hF b
  have := hF v₀
  apply (cancel_mono (F.map b.op)).1
  change ((F.map u₀.op ≫ inv (F.map v₀.op)) ≫ F.map v.op) ≫ F.map b.op = _
  calc
    _ = F.map u₀.op ≫ inv (F.map v₀.op) ≫ (F.map v.op ≫ F.map b.op) := by
      simp only [Category.assoc]
    _ = F.map u₀.op ≫ inv (F.map v₀.op) ≫ (F.map v₀.op ≫ F.map a.op) := by rw [← hj']
    _ = F.map u₀.op ≫ F.map a.op := by simp
    _ = _ := hi'

/-- The comparison with itself is the identity.
Source: identity refinement (blueprint: lem-pod-cofiltered-iso-comparison).
Proof: apply normalization to the identity cone and use the diagram's identity law. -/
theorem cofilteredIsoComparison_refl (i : C) :
    cofilteredIsoComparison F hF i i = Iso.refl _ := by
  apply Iso.ext
  simpa using cofilteredIsoComparison_normalized F hF (𝟙 i) (𝟙 i)

/-- Comparison composes strictly.
Source: common-refinement cocycle (blueprint: lem-pod-cofiltered-iso-comparison).
Proof: choose a cone over the three objects, normalize all three comparisons on it,
then cancel the invertible arrow to the third object. -/
theorem cofilteredIsoComparison_trans (i j k : C) :
    cofilteredIsoComparison F hF i j ≪≫ cofilteredIsoComparison F hF j k =
      cofilteredIsoComparison F hF i k := by
  let d₀ := IsCofiltered.min i j
  let d := IsCofiltered.min d₀ k
  let u : d ⟶ i := IsCofiltered.minToLeft d₀ k ≫ IsCofiltered.minToLeft i j
  let v : d ⟶ j := IsCofiltered.minToLeft d₀ k ≫ IsCofiltered.minToRight i j
  let w : d ⟶ k := IsCofiltered.minToRight d₀ k
  have := hF w
  apply Iso.ext
  apply (cancel_mono (F.map w.op)).1
  simp only [Iso.trans_hom, Category.assoc]
  rw [cofilteredIsoComparison_normalized F hF v w,
    cofilteredIsoComparison_normalized F hF u v,
    cofilteredIsoComparison_normalized F hF u w]

/-- Normalization determines the whole family up to strict equality.
Source: uniqueness by common refinement (blueprint: lem-pod-cofiltered-iso-comparison).
Proof: apply both normalizations to the chosen binary cone and cancel its second arrow;
isomorphism extensionality and function extensionality give equality of families. -/
theorem cofilteredIsoComparison_unique
    (σ : ∀ i j : C, F.obj (op i) ≅ F.obj (op j))
    (hσ : ∀ (i j d : C) (u : d ⟶ i) (v : d ⟶ j),
      (σ i j).hom ≫ F.map v.op = F.map u.op) :
    σ = cofilteredIsoComparison F hF := by
  funext i j
  apply Iso.ext
  let v := IsCofiltered.minToRight i j
  have := hF v
  apply (cancel_mono (F.map v.op)).1
  rw [hσ i j _ (IsCofiltered.minToLeft i j) v,
    cofilteredIsoComparison_normalized F hF (IsCofiltered.minToLeft i j) v]

end CategoryTheory

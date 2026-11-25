/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import WeilConjectures.CategoryTheory.SixFunctors.AlphaCompactObject
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckDerivedAlphaCompactRanks
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckDerivedAlphaCompactClasses

/-! # A common alpha-compact bound for an essentially small object class -/

@[expose] public section

universe v u

open CategoryTheory.Limits

open scoped ZeroObject

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

private theorem alphaCompact_common_bound
    {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{v} P]
    (hP : ∀ X, P X →
      ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular), IsAlphaCompact X κ) (β : Cardinal.{v}) :
    ∃ (α : Cardinal.{v}) (_ : Fact α.IsRegular), β ≤ α ∧
      ∀ X, P X → IsAlphaCompact X α := by
  classical
  obtain ⟨Q, hQsmall, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  have h (X : Subtype Q) :
      ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular), IsAlphaCompact X.1 κ :=
    hP X.1 (hQP _ X.2)
  choose κ hκ hX using h
  let R := Shrink.{v} (Subtype Q)
  let r : R → Subtype Q := (equivShrink.{v} (Subtype Q)).symm
  obtain ⟨α, hα, hlt⟩ := HasCardinalLT.exists_regular_cardinal_forall.{v}
    (Sum.elim (fun (_ : Unit) ↦ β.ord.ToType) (fun i : R ↦ (κ (r i)).ord.ToType))
  let _ : Fact α.IsRegular := ⟨hα⟩
  have hβ : β ≤ α := le_of_lt (by
    simpa [hasCardinalLT_iff_cardinal_mk_lt] using hlt (Sum.inl ⟨⟩))
  refine ⟨α, inferInstance, hβ, ?_⟩
  intro X hPX
  obtain ⟨Y, hQY, ⟨e⟩⟩ := hPQ X hPX
  let i : R := equivShrink.{v} (Subtype Q) ⟨Y, hQY⟩
  have hi : r i = ⟨Y, hQY⟩ := Equiv.symm_apply_apply _ _
  have hle : κ ⟨Y, hQY⟩ ≤ α := le_of_lt (by
    simpa [hasCardinalLT_iff_cardinal_mk_lt, hi] using hlt (Sum.inr i))
  let _ : Fact (κ ⟨Y, hQY⟩).IsRegular := hκ ⟨Y, hQY⟩
  exact ((hX ⟨Y, hQY⟩).of_le hle).of_iso e.symm

/-- The alpha-compact class supplied by the well-generation theorem.

Source: Neeman, Theorem 0.2; Krause, Sections 6.2--6.3.
(blueprint: new-sfb-derived-perfect-small-class-core-alpha)

Proof: choose a regular cardinal above a well-generation bound and above the
compactness ranks of representatives of `P`.  Let `S` be the class of
alpha-compact objects.  Neeman's well-generation theorem and Krause's
cardinal arguments give essential smallness, repleteness, triangulated closure,
closure under coproducts of fewer than `alpha` objects, and alpha-smallness.
The same cardinal bound makes every member of `P` alpha-compact; this last
fact is recorded separately so that the caller can derive `P ≤ S` by unfolding
`S` rather than hiding that step in the existence theorem.
-/
theorem derived_exists_alphaCompactClass_core
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (P : ObjectProperty (DerivedCategory A))
    [ObjectProperty.EssentiallySmall.{v} P] :
    ∃ (S : ObjectProperty (DerivedCategory A)) (α : Cardinal.{v})
      (_ : Fact α.IsRegular),
      (∀ U, S U ↔ IsAlphaCompact U α) ∧
      ObjectProperty.EssentiallySmall.{v} S ∧ S.IsClosedUnderIsomorphisms ∧
      S.IsTriangulated ∧
      (∀ (I : Type v) (Y : I → DerivedCategory A),
        HasCardinalLT I α → (∀ i, S (Y i)) → S (∐ Y)) ∧
      (∀ U, S U → IsAlphaCompact U α) ∧
      (∀ U, P U → IsAlphaCompact U α) := by
  obtain ⟨β, hβ, hclasses⟩ := derived_alphaCompact_classes_eventually_small (A := A)
  obtain ⟨α, hα, hβα, hP⟩ := alphaCompact_common_bound P
    (fun U _ ↦ derived_exists_alphaCompact_rank U) β
  let _ : Fact α.IsRegular := hα
  obtain ⟨hSmall, hExt⟩ := hclasses α hβα
  let S := alphaCompactObjects (DerivedCategory A) α
  let _ : S.IsTriangulatedClosed₂ := hExt
  let _ : S.ContainsZero := ⟨0, isZero_zero _, isAlphaCompact_zero α⟩
  let _ : S.IsStableUnderShift ℤ := ⟨fun n ↦
    ObjectProperty.IsStableUnderShiftBy.mk (fun U hU ↦ hU.shift n)⟩
  have hTri : S.IsTriangulated := {}
  exact ⟨alphaCompactObjects (DerivedCategory A) α, α, hα,
    fun _ ↦ Iff.rfl, hSmall, inferInstance, hTri,
    fun I Y hI hY ↦ IsAlphaCompact.coproduct α I Y hI hY, fun _ h ↦ h, hP⟩

end CategoryTheory

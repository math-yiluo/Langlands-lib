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
import WeilConjectures.CategoryTheory.IsAlphaCompact.AlphaCompactObjectProperties
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckDerivedPerfectWellGenerators
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckDerivedAlphaCompactClasses

/-! # Alpha-compact ranks in a Grothendieck derived category -/

@[expose] public section

universe v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

open scoped ZeroObject

namespace CategoryTheory

attribute [local instance] derived_hasCoproducts

/-- Every object of a Grothendieck derived category has an alpha-compact rank.

Source: Neeman, On the derived category of sheaves on a manifold, Theorem 0.2
and Section 2; Krause, On Neeman's Well Generated Triangulated Categories (2001),
page 125, Corollary of Theorem A.
(blueprint: new-sfb-derived-alpha-compact-ranks)

Proof in words: take a small perfect generating class G at rank kappa, and a
regular beta above which the canonical alpha-compact classes are extension closed.
Let S consist of objects compact at some regular rank. It contains zero and is
replete and closed under shifts by the alpha-compact API. For a distinguished
triangle, choose one regular alpha above beta and the ranks of its outer vertices;
monotonicity and canonical extension closure put its middle vertex in S.
For a v-small family in S, choose ranks for all members and a common regular alpha
above beta, the cardinality of the index, and these ranks. Its coproduct is then
alpha-compact by bounded coproduct closure. Thus S is a localizing class.
Each member of G is kappa-compact using G itself as the (G3)--(G4) witness.
Generation by G forces S to contain every object. In particular U has a regular
alpha-compact rank. This proves the union assertion without assuming it in a
new theorem or using ordinary presentability.
-/
theorem derived_exists_alphaCompact_rank
    {A : Type u} [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{v} A] [HasDerivedCategory.{v} A]
    (U : DerivedCategory A) :
    ∃ (α : Cardinal.{v}) (_ : Fact α.IsRegular), IsAlphaCompact U α := by
  classical
  obtain ⟨G, κ, hκ, hGsmall, hGshift, hGsmallness, hGfactor, hGgen⟩ :=
    derived_exists_perfect_well_generators (A := A)
  obtain ⟨β, hβ, hclasses⟩ := derived_alphaCompact_classes_eventually_small (A := A)
  let S : ObjectProperty (DerivedCategory A) := fun X ↦
    ∃ (α : Cardinal.{v}) (_ : Fact α.IsRegular), IsAlphaCompact X α
  let _ : S.IsClosedUnderIsomorphisms := ⟨by
    rintro X Y e ⟨α, hα, hX⟩
    exact ⟨α, hα, hX.of_iso e⟩⟩
  let _ : S.ContainsZero := ⟨0, isZero_zero _, β, hβ, by
    let _ : Fact β.IsRegular := hβ
    exact isAlphaCompact_zero β⟩
  let _ : S.IsStableUnderShift ℤ := ⟨fun n ↦
    ObjectProperty.IsStableUnderShiftBy.mk (by
      rintro X ⟨α, hα, hX⟩
      exact ⟨α, hα, hX.shift n⟩)⟩
  let _ : S.IsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    rintro T hT ⟨α₁, hα₁, h₁⟩ ⟨α₃, hα₃, h₃⟩
    let F : Unit ⊕ Bool → Type v :=
      Sum.elim (fun _ ↦ β.ord.ToType)
        (fun b ↦ (if b then α₁ else α₃).ord.ToType)
    obtain ⟨α, hα, hlt⟩ := HasCardinalLT.exists_regular_cardinal_forall.{v} F
    let _ : Fact α.IsRegular := ⟨hα⟩
    have hβα : β ≤ α := le_of_lt (by
      simpa [F, hasCardinalLT_iff_cardinal_mk_lt] using hlt (Sum.inl ⟨⟩))
    have hα₁α : α₁ ≤ α := le_of_lt (by
      simpa [F, hasCardinalLT_iff_cardinal_mk_lt] using hlt (Sum.inr true))
    have hα₃α : α₃ ≤ α := le_of_lt (by
      simpa [F, hasCardinalLT_iff_cardinal_mk_lt] using hlt (Sum.inr false))
    let _ := (hclasses α hβα).2
    exact ⟨α, inferInstance,
      (alphaCompactObjects (DerivedCategory A) α).ext_of_isTriangulatedClosed₂ T hT
        (h₁.of_le hα₁α) (h₃.of_le hα₃α)⟩)
  let _ : S.IsTriangulated := {}
  have hSsum : ∀ (I : Type v) (Y : I → DerivedCategory A),
      (∀ i, S (Y i)) → S (∐ Y) := by
    intro I Y hY
    choose αi hαi hYi using hY
    let F : Option I → Type v := fun i ↦
      match i with
      | none => I
      | some i => (αi i).ord.ToType
    obtain ⟨α, hα, hlt⟩ := HasCardinalLT.exists_regular_cardinal_forall.{v} F
    let _ : Fact α.IsRegular := ⟨hα⟩
    have hI : HasCardinalLT I α := hlt none
    have hle (i : I) : αi i ≤ α := le_of_lt (by
      simpa [F, hasCardinalLT_iff_cardinal_mk_lt] using hlt (some i))
    exact ⟨α, inferInstance, IsAlphaCompact.coproduct α I Y hI
      (fun i ↦ (hYi i).of_le (hle i))⟩
  have hGS : G ≤ S := fun X hX ↦ ⟨κ, hκ, G, hX, hGsmallness, hGfactor⟩
  exact hGgen S hSsum hGS U

end CategoryTheory

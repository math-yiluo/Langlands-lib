/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.CategoryTheory.CompactCone

/-!
# Compact objects form a thick subcategory

Source: Stacks Project, Derived Categories, Lemma 13.37.2 (Tag 09QH)
(blueprint: lem-sc-compact-objects-thick).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

open scoped ZeroObject

private theorem compact_retract
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    {K L : C} (r : Retract K L) (hL : IsCompactObject L) : IsCompactObject K := by
  classical
  intro J A
  let cK := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp K (Sigma.ι A j))
  let cL := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp L (Sigma.ι A j))
  let d := DirectSum.map (fun j ↦ Preadditive.leftComp (A j) r.r)
  let e := DirectSum.map (fun j ↦ Preadditive.leftComp (A j) r.i)
  have hd (x) : cL (d x) = r.r ≫ cK x :=
    DFunLike.congr_fun (compact_comparison_naturality r.r A) x
  have he (x) : cK (e x) = r.i ≫ cL x :=
    DFunLike.congr_fun (compact_comparison_naturality r.i A) x
  have hed (x) : e (d x) = x := by
    ext j
    simp only [e, d, DirectSum.map_apply]
    change r.i ≫ r.r ≫ x j = x j
    rw [← Category.assoc, r.retract, Category.id_comp]
  constructor
  · intro x y hxy
    have h : d x = d y := (hL J A).1 (by rw [hd, hd, hxy])
    exact (hed x).symm.trans ((congrArg e h).trans (hed y))
  · intro f
    obtain ⟨x, hx⟩ := (hL J A).2 (r.r ≫ f)
    refine ⟨e x, ?_⟩
    change cK (e x) = f
    rw [he]
    rw [hx, ← Category.assoc, r.retract, Category.id_comp]

private theorem compact_zero
    {C : Type u} [Category.{v} C] [HasZeroObject C]
    [Preadditive C] [HasCoproducts.{w} C] : IsCompactObject (0 : C) := by
  classical
  intro J A
  constructor
  · intro x y hxy
    ext j
  · intro f
    refine ⟨0, ?_⟩
    exact (isZero_zero C).eq_of_src _ _

/-- Compact objects are closed under thick operations.
Source: Stacks Project, Derived Categories, Lemma 13.37.2, Tag 09QH.
(blueprint: lem-sc-compact-objects-thick).

Proof: the zero object is compact since all its Hom groups are zero. The adjunction
between a shift and its inverse, and preservation of coproducts by both equivalences,
identify the shifted compact-Hom comparison with the original one. Thus compactness
is stable under shifts. For a distinguished triangle with two compact terms, the
comparison maps fit into a morphism of five-term exact Hom sequences. The row of
direct sums is exact, since direct sums of abelian groups preserve exactness; the
other row is exact by the homological property of representable functors. The four
outer comparisons are bijective by compactness of the two known terms and their
shifts. The five lemma proves bijectivity for the remaining term. Rotate triangles
to obtain closure for every pair of terms. Finally, an isomorphism of sources
identifies the comparison maps by precomposition. For a retract of a compact object,
precomposition with its retraction and inclusion expresses the comparison map as a
retract of a bijection, so it is bijective too. These facts give exactly the two
asserted object-property classes. -/
theorem compactObjects_isThick
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [HasCoproducts.{w} C] :
    ObjectProperty.IsTriangulated (fun K : C ↦ IsCompactObject K) ∧
      ObjectProperty.IsStableUnderRetracts (fun K : C ↦ IsCompactObject K) := by
  let R : ObjectProperty C := fun K ↦ IsCompactObject K
  let : R.IsStableUnderRetracts := ⟨fun r hL ↦ compact_retract r hL⟩
  let : R.ContainsZero := ⟨0, isZero_zero C, compact_zero⟩
  let : R.IsStableUnderShift ℤ := ⟨fun n ↦
    ObjectProperty.IsStableUnderShiftBy.mk (fun K hK ↦ compact_shift K hK n)⟩
  let : R.IsTriangulatedClosed₃ := ObjectProperty.IsTriangulatedClosed₃.mk'
    (fun T hT h₁ h₂ ↦ compact_cone T hT h₁ h₂)
  let : R.IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  exact ⟨{}, inferInstance⟩

end CategoryTheory

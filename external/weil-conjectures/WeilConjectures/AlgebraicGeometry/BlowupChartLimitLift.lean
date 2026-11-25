/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BlowupChartLimitPushout
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Elements of charts over a filtered colimit of rings come from a finite stage

Let `R` be the colimit of a filtered diagram `D : K ⥤ CommRingCat`. Every polynomial over `R`
comes from a polynomial over some `D(j)`, and every element of a chart `R[T]/(x'T - y')` of a
blow-up, with `x', y'` coming from `D(k₀)`, comes from the corresponding chart over some
`D(k₁)` with `k₀ ⟶ k₁` (`AlgebraicGeometry.exists_blowupChart_lift`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {K : Type u} [SmallCategory K] [IsFiltered K] {D : K ⥤ CommRingCat.{u}} {c : Cocone D}
  (hc : IsColimit c)

include hc in
/-- Every polynomial over a filtered colimit of rings comes from a polynomial over some stage. -/
theorem exists_polynomial_lift (p : c.pt[X]) :
    ∃ (j : K) (q : (D.obj j)[X]), q.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨j₁, q₁, rfl⟩ := h₁
    obtain ⟨j₂, q₂, rfl⟩ := h₂
    refine ⟨IsFiltered.max j₁ j₂, q₁.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom +
      q₂.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w]
  | monomial n a =>
    obtain ⟨j, b, rfl⟩ := Concrete.isColimit_exists_rep D hc a
    exact ⟨j, Polynomial.monomial n b, by simp⟩

include hc in
/-- **Elements of a chart of a blow-up over a filtered colimit come from a finite stage.** If
`x' y' ∈ R = colim D` are the images of `x y ∈ D(k₀)`, every element `u` of the chart
`R[T]/(x'T - y')` is the image of an element of the chart `D(k₁)[T]/(x₁T - y₁)` for some
`f : k₀ ⟶ k₁`, where `x₁, y₁` are the images of `x, y` in `D(k₁)`. -/
theorem exists_blowupChart_lift (k₀ : K) {x y : D.obj k₀} {x' y' : c.pt}
    (hx : (c.ι.app k₀).hom x = x') (hy : (c.ι.app k₀).hom y = y') (u : blowupChart x' y') :
    ∃ (k₁ : K) (f : k₀ ⟶ k₁) (uA : blowupChart ((D.map f).hom x) ((D.map f).hom y))
      (hx₁ : (c.ι.app k₁).hom ((D.map f).hom x) = x')
      (hy₁ : (c.ι.app k₁).hom ((D.map f).hom y) = y'),
      blowupChartMap (c.ι.app k₁).hom hx₁ hy₁ uA = u := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hc' : IsColimit (c.whisker (Under.forget k₀)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget k₀) c).symm hc
  obtain ⟨X, q, hq⟩ := exists_polynomial_lift hc' p
  change (D.obj X.right)[X] at q
  have hw (z : D.obj k₀) : (c.ι.app X.right).hom ((D.map X.hom).hom z) = (c.ι.app k₀).hom z := by
    exact congr($(c.w X.hom).hom z)
  exact ⟨X.right, X.hom, Ideal.Quotient.mk _ q, (hw x).trans hx, (hw y).trans hy,
    by rw [blowupChartMap_mk]; exact congr(Ideal.Quotient.mk _ $hq)⟩

end AlgebraicGeometry

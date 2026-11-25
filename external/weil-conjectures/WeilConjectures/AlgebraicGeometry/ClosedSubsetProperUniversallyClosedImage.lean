/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Images of closed subsets proper over a base

Source: Stacks Project, Cohomology of Schemes, Lemma 30.26.5 (Tag 0CYQ), part (2).
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The image of a closed subset proper over the base under a universally closed
morphism over that base is closed and proper over the base.
Source: Stacks Project, Tag 0CYQ, part (2).
(blueprint: lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image)

Proof:
1. Universal closedness makes `f(Z)` closed. Give `Z` and `Z' = f(Z)` their reduced
   induced closed subscheme structures using
   `lem-weil-pbc-reduced-induced-closed-subscheme`. Form `Z'' = X ×[Y] Z'`
   (`def-pc-fibre-product`); the reduced source factors through it by
   `lem-weil-pbc-reduced-source-factors-through-closed-subscheme` (Tag 0356).
2. The projection `Z'' → Z'` is universally closed by
   `lem-weil-pbc-universally-closed-base-change`. The map `Z → Z''` is a closed
   immersion by `lem-weil-pbc-closed-immersion-cancellation`, using
   `lem-weil-pbc-closed-immersion-base-change` for `Z'' → X`. Composition
   (`lem-weil-pbc-closed-immersion-integral-separated-uc`) makes `Z → Z'`
   universally closed; it is surjective by its underlying image.
3. Properness of `Z → S` supplies separatedness. Descend it along the surjective
   universally closed map using `lem-weil-pbc-surjective-universally-closed-separated`.
4. The closed immersion `Z' → Y` and the locally finite type map `Y → S` give
   local finite type for `Z' → S` by `lem-weil-pbc-proper-fp-permanence`.
5. Descend universal closedness of `Z → S` along `Z → Z'` by
   `lem-weil-pbc-image-universally-closed` (Tag 03GN). Together with separatedness
   and local finite type this proves properness of `Z' → S`. -/
theorem image_isClosedSubsetProperOver_of_universallyClosed
    {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (f : X ⟶ Y) (hf : f ≫ q = p) [UniversallyClosed f]
    (Z : TopologicalSpace.Closeds X) (hZ : IsClosedSubsetProperOver p Z) :
    ∃ Z' : TopologicalSpace.Closeds Y,
      (Z' : Set Y) = f '' (Z : Set X) ∧ IsClosedSubsetProperOver q Z' := by
  classical
  let i := (IdealSheafData.vanishingIdeal Z).subschemeι
  let h := i ≫ f
  have hi : Set.range i = (Z : Set X) := by simp [i]
  have hr : Set.range h = f '' (Z : Set X) := by
    change Set.range (i ≫ f).base = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hi]
  let W : TopologicalSpace.Closeds Y := ⟨Set.range h, h.isClosedMap.isClosed_range⟩
  have hker : h.ker = IdealSheafData.vanishingIdeal W := by
    rw [h.ker_eq_vanishingIdeal]
    congr 1
    apply TopologicalSpace.Closeds.ext
    exact h.isClosedMap.isClosed_range.closure_eq
  have hp : IsProper (h ≫ q) := by
    change IsProper (i ≫ f ≫ q)
    rw [hf]
    exact hZ
  have : IsProper (h.toImage ≫ h.imageι ≫ q) := by
    rw [← Category.assoc, h.toImage_imageι]
    exact hp
  have : IsSeparated (h.imageι ≫ q) :=
    isSeparated_of_surjective_universallyClosed (h ≫ q) (h.imageι ≫ q)
      h.toImage (by rw [← Category.assoc, h.toImage_imageι])
  have : UniversallyClosed (h.imageι ≫ q) :=
    UniversallyClosed.of_comp_surjective h.toImage (h.imageι ≫ q)
  refine ⟨W, hr, ?_⟩
  change IsProper ((IdealSheafData.vanishingIdeal W).subschemeι ≫ q)
  rw [← hker]
  exact {}

end AlgebraicGeometry.Scheme

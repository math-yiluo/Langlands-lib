/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
/-! # The union of a cocone's triangulated essential images

Morphism descent lets one construct a cone at a common stage. Thus the union of the
essential images is triangulated even when no individual stage functor is full.
-/
@[expose] public section
universe w v u v' u'
open CategoryTheory Limits ZeroObject Pretriangulated
namespace CategoryTheory.CategoryCocone
variable {I : Type w} [Preorder I] [Nonempty I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, HasZeroObject (C i)] [∀ i, Preadditive (C i)] [∀ i, HasShift (C i) ℤ]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (c : CategoryCocone C D) [∀ i, (c.Φ i).CommShift ℤ] [∀ i, (c.Φ i).IsTriangulated]

/-- If all morphisms between images descend, the union of the essential images is
triangulated.
Source: upstream master, ModuleObject/Colimit/TwoColimit.lean, Postnikov object descent
(auxiliary; not a blueprint node).

Proof: zero is the image of zero at any stage. Shift a model and use the functor's shift
comparison. Isomorphism closure follows by composing the witnessing isomorphisms.
For a triangle whose first two objects have models, conjugate its first arrow by their
model isomorphisms and descend the resulting arrow to a common stage. Complete it to a
distinguished triangle there. Its image and the original triangle have isomorphic first
arrows, so their third objects are isomorphic. This proves closure under cones. Together
with shifts it proves closure under extensions, by inverse rotation. The index need only
be nonempty: the morphism-descent hypothesis itself provides every required common stage. -/
theorem isTriangulated_exists_essImage (hc : c.HomSurj) :
    ObjectProperty.IsTriangulated (fun Y ↦ ∃ i, (c.Φ i).essImage Y) := by
  let P : ObjectProperty D := fun Y ↦ ∃ i, (c.Φ i).essImage Y
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨i, h⟩ ↦ ⟨i, (c.Φ i).essImage.prop_of_iso e h⟩⟩
  have : P.IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun Y ⟨i, X, ⟨e⟩⟩ ↦
      ⟨i, X⟦n⟧, ⟨((c.Φ i).commShiftIso n).app X ≪≫
        (shiftFunctor D n).mapIso e⟩⟩⟩⟩
  have : P.IsTriangulatedClosed₃ := .mk' (by
    rintro T hT ⟨i, X, ⟨ex⟩⟩ ⟨j, Y, ⟨ey⟩⟩
    obtain ⟨k, hi, hj, g, hg⟩ := hc i j X Y (ex.hom ≫ T.mor₁ ≫ ey.inv)
    obtain ⟨Z, b, d, hd⟩ := distinguished_cocone_triangle g
    let ex' := (c.iso hi).app X ≪≫ ex
    let ey' := (c.iso hj).app Y ≪≫ ey
    have hcomm : (c.Φ k).map g ≫ ey'.hom = ex'.hom ≫ T.mor₁ := by
      dsimp only [ex', ey', Iso.trans_hom, Iso.app_hom]
      apply (cancel_epi ((c.iso hi).inv.app X)).1
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using congrArg (· ≫ ey.hom) hg.symm
    exact ⟨k, Z, ⟨Triangle.π₃.mapIso
      (isoTriangleOfIso₁₂ _ _ ((c.Φ k).map_distinguished _ hd) hT ex' ey' hcomm)⟩⟩)
  have : P.IsTriangulatedClosed₂ := .of_isTriangulatedClosed₃
  refine { exists_zero := ?_ }
  let i := Classical.choice (inferInstance : Nonempty I)
  exact ⟨0, isZero_zero D, i, 0, ⟨(c.Φ i).mapZeroObject⟩⟩
end CategoryTheory.CategoryCocone

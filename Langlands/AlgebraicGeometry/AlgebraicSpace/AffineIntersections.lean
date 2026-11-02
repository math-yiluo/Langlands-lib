import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine intersections for presheaves with closed diagonal -/

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

private theorem isPullback_diag_of_isPullback
    {C : Type v} [Category.{w} C] [HasBinaryProducts C]
    {P X Y Z : C} {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) :
    IsPullback (p ≫ f) (prod.lift p q) (Limits.diag Z) (prod.map f g) := by
  have hw : (p ≫ f) ≫ Limits.diag Z = prod.lift p q ≫ prod.map f g := by
    apply prod.hom_ext <;> simp [h.w]
  apply IsPullback.of_isLimit' ⟨hw⟩
  refine PullbackCone.IsLimit.mk _
    (fun c => h.lift (c.snd ≫ prod.fst) (c.snd ≫ prod.snd) ?_) ?_ ?_ ?_
  · have h1 := congrArg (fun k => k ≫ prod.fst) c.condition
    have h2 := congrArg (fun k => k ≫ prod.snd) c.condition
    simp only [Category.assoc, Limits.diag, prod.lift_fst, prod.lift_snd,
      prod.map_fst, prod.map_snd, Category.comp_id] at h1 h2
    simpa only [Category.assoc] using h1.symm.trans h2
  · intro c
    have hc := congrArg (fun k => k ≫ prod.fst) c.condition
    simpa using hc.symm
  · intro c
    apply prod.hom_ext <;> simp
  · intro c m hm1 hm2
    apply h.hom_ext
    · have hc := congrArg (fun k => k ≫ prod.fst) hm2
      simpa using hc
    · have hc := congrArg (fun k => k ≫ prod.snd) hm2
      simpa using hc

variable {S : Scheme.{u}} {F : Presheaf S}

/-- A represented fibre product maps by a closed immersion into the product
of its two representing schemes, when the target presheaf has closed diagonal. -/
theorem closedImmersion_pair_of_isPullback
    (hF : IsClosedImmersion (Limits.diag F))
    {V V1 V2 : Over S} (a1 : (schemeYoneda S).obj V1 ⟶ F)
    (a2 : (schemeYoneda S).obj V2 ⟶ F) (p1 : V ⟶ V1) (p2 : V ⟶ V2)
    (h : IsPullback ((schemeYoneda S).map p1) ((schemeYoneda S).map p2) a1 a2) :
    _root_.AlgebraicGeometry.IsClosedImmersion (prod.lift p1 p2).left := by
  have hd := isPullback_diag_of_isPullback h
  have hd' : IsPullback ((schemeYoneda S).map p1 ≫ a1) ((schemeYoneda S).map (prod.lift p1 p2))
      (Limits.diag F)
      (prod.lift ((schemeYoneda S).map prod.fst ≫ a1) ((schemeYoneda S).map prod.snd ≫ a2)) := by
    apply hd.of_iso' (Iso.refl _) (Iso.refl _)
      (asIso (prodComparison (schemeYoneda S) V1 V2)) (Iso.refl _)
    · simp
    · apply prod.hom_ext <;> simp [prodComparison, ← Functor.map_comp]
    · simp
    · apply prod.hom_ext <;> simp [prodComparison]
  exact hF.projection _ _ _ hd'

/-- Over an affine base, the product of two affine schemes in the slice is affine. -/
theorem isAffine_slice_product [IsAffine S] (V1 V2 : Over S)
    [IsAffine V1.left] [IsAffine V2.left] : IsAffine (V1 ⨯ V2).left := by
  exact IsAffine.of_isIso (Over.prodLeftIsoPullback V1 V2).hom

/-- Over an affine base, any represented intersection of affine charts of a
presheaf with closed diagonal is affine. -/
theorem isAffine_of_isPullback_of_closedDiagonal [IsAffine S]
    (hF : IsClosedImmersion (Limits.diag F))
    {V V1 V2 : Over S} [IsAffine V1.left] [IsAffine V2.left]
    (a1 : (schemeYoneda S).obj V1 ⟶ F)
    (a2 : (schemeYoneda S).obj V2 ⟶ F) (p1 : V ⟶ V1) (p2 : V ⟶ V2)
    (h : IsPullback ((schemeYoneda S).map p1) ((schemeYoneda S).map p2) a1 a2) :
    IsAffine V.left := by
  let := isAffine_slice_product V1 V2
  let := closedImmersion_pair_of_isPullback hF a1 a2 p1 p2 h
  exact isAffine_of_isAffineHom (prod.lift p1 p2).left

/-- Two affine open charts of a presheaf with closed diagonal over an affine
base have an actual affine represented fibre product with both projections open. -/
theorem exists_affine_open_intersection [IsAffine S]
    (hF : IsClosedImmersion (Limits.diag F))
    {V1 V2 : Over S} [IsAffine V1.left] [IsAffine V2.left]
    (a1 : (schemeYoneda S).obj V1 ⟶ F) (ha1 : IsOpenImmersion a1)
    (a2 : (schemeYoneda S).obj V2 ⟶ F) (ha2 : IsOpenImmersion a2) :
    ∃ (V : Over S) (p1 : V ⟶ V1) (p2 : V ⟶ V2),
      IsAffine V.left ∧ _root_.AlgebraicGeometry.IsOpenImmersion p1.left ∧
      _root_.AlgebraicGeometry.IsOpenImmersion p2.left ∧
      IsPullback ((schemeYoneda S).map p1) ((schemeYoneda S).map p2) a1 a2 := by
  let hr := ha1.representable
  let p1 := Functor.relativelyRepresentable.fst' hr a2
  let p2 := hr.snd a2
  have h : IsPullback ((schemeYoneda S).map p1) ((schemeYoneda S).map p2) a1 a2 :=
    Functor.relativelyRepresentable.isPullback' hr a2
  exact ⟨hr.pullback a2, p1, p2,
    isAffine_of_isPullback_of_closedDiagonal hF a1 a2 p1 p2 h,
    ha2.projection a1 _ p1 h.flip, ha1.projection a2 _ p2 h, h⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace

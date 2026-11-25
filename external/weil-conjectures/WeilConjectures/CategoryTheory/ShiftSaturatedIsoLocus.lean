/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! Invertibility on all shifts of an object is a localizing predicate for a
natural transformation between exact functors. The transformation itself need
not commute with the chosen shifts. Source: the five-term exact-sequence
argument, already used privately in FlatTelescopeNormalizationUnshiftedIsIso.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.ShiftSaturated
/-- Five-term exactness detects the middle isomorphism. The two maps on shifted
objects are independent supplied maps, rather than shifts of the first two.
Proof: coyoneda exactness gives injectivity by cancellation with `d`, and
surjectivity by lifting the connecting image through `d` and correcting through
`b`; Yoneda then detects the isomorphism. -/
private theorem cone_five_lemma
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T T' : Triangle C} (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (a : T.obj₁ ⟶ T'.obj₁) (b : T.obj₂ ⟶ T'.obj₂) (c : T.obj₃ ⟶ T'.obj₃)
    (d : T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₁⟦(1 : ℤ)⟧)
    (e : T.obj₂⟦(1 : ℤ)⟧ ⟶ T'.obj₂⟦(1 : ℤ)⟧)
    [IsIso a] [IsIso b] [IsIso d] [IsIso e]
    (h₁ : T.mor₁ ≫ b = a ≫ T'.mor₁)
    (h₂ : T.mor₂ ≫ c = b ≫ T'.mor₂)
    (h₃ : T.mor₃ ≫ d = c ≫ T'.mor₃)
    (h₄ : T.mor₁⟦(1 : ℤ)⟧' ≫ e = d ≫ T'.mor₁⟦(1 : ℤ)⟧') : IsIso c := by
  have : Mono c := by
    rw [Preadditive.mono_iff_cancel_zero]
    intro A x hx
    obtain ⟨y, rfl⟩ := T.coyoneda_exact₃ hT x (by
      rw [← cancel_mono d, Category.assoc, h₃, reassoc_of% hx,
        zero_comp, zero_comp])
    have hy : (y ≫ b) ≫ T'.mor₂ = 0 := by
      rw [Category.assoc, ← h₂, ← Category.assoc]
      exact hx
    obtain ⟨z, hz⟩ := T'.coyoneda_exact₂ hT' (y ≫ b) hy
    have heq : y = (z ≫ inv a) ≫ T.mor₁ := by
      apply (cancel_mono b).1
      rw [Category.assoc, h₁]
      simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hz
    rw [heq, Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]
  apply isIso_of_yoneda_map_bijective c
  intro A
  constructor
  · intro x y h
    exact (cancel_mono c).1 h
  · intro y
    let x₄ := y ≫ T'.mor₃ ≫ inv d
    have hx₄ : x₄ ≫ T.mor₁⟦(1 : ℤ)⟧' = 0 := by
      apply (cancel_mono e).1
      dsimp only [x₄]
      rw [Category.assoc, Category.assoc, h₄]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc,
        comp_distTriang_mor_zero₃₁ T' hT', comp_zero, zero_comp]
    obtain ⟨x, hx⟩ := T.coyoneda_exact₁ hT x₄ hx₄
    have hxc : x ≫ c ≫ T'.mor₃ = y ≫ T'.mor₃ := by
      rw [← h₃, ← Category.assoc, ← hx]
      dsimp only [x₄]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨z, hz⟩ := T'.coyoneda_exact₃ hT' (y - x ≫ c) (by
      rw [Preadditive.sub_comp, Category.assoc, hxc, sub_self])
    refine ⟨x + (z ≫ inv b) ≫ T.mor₂, ?_⟩
    change (x + (z ≫ inv b) ≫ T.mor₂) ≫ c = y
    rw [Preadditive.add_comp, Category.assoc, h₂]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← hz]
    exact add_sub_cancel _ _



/-- Naturality and the two exact functor structures form five-term commuting
rows. Transport the independently invertible components at `A[1]` and `B[1]`
through the shift isomorphisms and apply `cone_five_lemma`.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
theorem isoOnThirdOfIsoOnFour
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (τ : F ⟶ G)
    (T : Triangle C) (hT : T ∈ distTriang C)
    [IsIso (τ.app T.obj₁)] [IsIso (τ.app T.obj₂)]
    [IsIso (τ.app (T.obj₁⟦(1 : ℤ)⟧))]
    [IsIso (τ.app (T.obj₂⟦(1 : ℤ)⟧))] : IsIso (τ.app T.obj₃) := by
  let d := (F.commShiftIso (1 : ℤ)).inv.app T.obj₁ ≫
    τ.app (T.obj₁⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁
  let e := (F.commShiftIso (1 : ℤ)).inv.app T.obj₂ ≫
    τ.app (T.obj₂⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₂
  apply cone_five_lemma (F.map_distinguished T hT) (G.map_distinguished T hT)
    (τ.app T.obj₁) (τ.app T.obj₂) (τ.app T.obj₃) d e
  · exact τ.naturality T.mor₁
  · exact τ.naturality T.mor₂
  · change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ d =
      τ.app T.obj₃ ≫ (G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
    dsimp [d]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [τ.naturality_assoc]
  · change (F.map T.mor₁)⟦(1 : ℤ)⟧' ≫ e = d ≫ (G.map T.mor₁)⟦(1 : ℤ)⟧'
    dsimp [d, e]
    rw [← Category.assoc, F.commShiftIso_inv_naturality]
    simp only [Category.assoc]
    rw [τ.naturality_assoc, G.commShiftIso_hom_naturality]


section Saturation
variable {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
  (F G : C ⥤ D) (τ : F ⟶ G)

/-- The isomorphism locus saturated under every integer shift.
Source: the all-shifts predicate in the five-term exact-sequence argument.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
def isoOnAllShifts (X : C) : Prop := ∀ n : ℤ, IsIso (τ.app (X⟦n⟧))

/-- Invertibility on all shifts is invariant under object isomorphism.
Proof: apply naturality to the image of the isomorphism under each shift functor.
Source: `NatTrans.isIso_app_iff_of_iso`.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
theorem isoOnAllShifts_of_iso {X Y : C} (e : X ≅ Y)
    (h : isoOnAllShifts F G τ X) : isoOnAllShifts F G τ Y := by
  intro n
  exact (NatTrans.isIso_app_iff_of_iso τ ((shiftFunctor C n).mapIso e)).mp (h n)

/-- Invertibility on all shifts is preserved by any further integer shift.
Proof: transport the component at n + m through the shift-add isomorphism.
Source: `shiftFunctorAdd` and naturality.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
theorem isoOnAllShifts_shift {X : C} (h : isoOnAllShifts F G τ X) (n : ℤ) :
    isoOnAllShifts F G τ (X⟦n⟧) := by
  intro m
  exact (NatTrans.isIso_app_iff_of_iso τ ((shiftFunctorAdd C n m).app X)).mp (h (n + m))

/-- Invertibility on all shifts descends to retracts.
Proof: shift the retraction and use the induced retraction of component arrows.
Source: `NatTrans.retractArrowApp` and `MorphismProperty.of_retract`.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
theorem isoOnAllShifts_retract {X Y : C} (r : Retract X Y)
    (h : isoOnAllShifts F G τ Y) : isoOnAllShifts F G τ X := by
  intro n
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
    (τ.retractArrowApp (r.map (shiftFunctor C n))) (h n)

/-- Invertibility on all shifts passes to coproducts preserved by both functors.
Proof: whisker the transformation by each shift equivalence, which preserves colimits,
then use invertibility on the summands to detect invertibility on the colimit point.
This also covers an empty index set.
Source: `isIso_app_coconePt_of_preservesColimit`.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
theorem isoOnAllShifts_coproduct
    {J : Type*} (E : J → C) (q : Cofan E) (hq : IsColimit q)
    [PreservesColimitsOfShape (Discrete J) F] [PreservesColimitsOfShape (Discrete J) G]
    (h : ∀ j, isoOnAllShifts F G τ (E j)) : isoOnAllShifts F G τ q.pt := by
  intro n
  let σ := Functor.whiskerLeft (shiftFunctor C n) τ
  have : ∀ j : Discrete J,
      IsIso ((Functor.whiskerLeft (Discrete.functor E) σ).app j) := fun j ↦ h j.as n
  have : IsIso (Functor.whiskerLeft (Discrete.functor E) σ) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit (Discrete.functor E) σ q hq

variable [HasZeroObject C] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]

/-- Invertibility on all shifts passes to the third object of a distinguished triangle.
Proof: shift the triangle by n, supply invertibility at its first two objects and their
further shifts by one, and apply the four-component five-term lemma for every n.
Source: `Triangle.shift_distinguished` and `isoOnThirdOfIsoOnFour` above.
(blueprint: lem-sc-shift-saturated-iso-locus). -/
theorem isoOnAllShifts_cone (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : isoOnAllShifts F G τ T.obj₁) (h₂ : isoOnAllShifts F G τ T.obj₂) :
    isoOnAllShifts F G τ T.obj₃ := by
  intro n
  let Tn := (Triangle.shiftFunctor C n).obj T
  let : IsIso (τ.app Tn.obj₁) := by
    change IsIso (τ.app (T.obj₁⟦n⟧))
    exact h₁ n
  let : IsIso (τ.app Tn.obj₂) := by
    change IsIso (τ.app (T.obj₂⟦n⟧))
    exact h₂ n
  let : IsIso (τ.app (Tn.obj₁⟦(1 : ℤ)⟧)) := by
    change IsIso (τ.app ((T.obj₁⟦n⟧)⟦(1 : ℤ)⟧))
    exact isoOnAllShifts_shift F G τ h₁ n 1
  let : IsIso (τ.app (Tn.obj₂⟦(1 : ℤ)⟧)) := by
    change IsIso (τ.app ((T.obj₂⟦n⟧)⟦(1 : ℤ)⟧))
    exact isoOnAllShifts_shift F G τ h₂ n 1
  exact isoOnThirdOfIsoOnFour F G τ Tn (Triangle.shift_distinguished T hT n)
end Saturation

end CategoryTheory.ShiftSaturated

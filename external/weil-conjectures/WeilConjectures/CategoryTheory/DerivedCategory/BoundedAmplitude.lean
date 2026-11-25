/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Amplitude of a triangulated functor on bounded objects

Let `G : D(C) ⥤ D(D)` be a triangulated functor between derived categories. If `G` sends every
object of `C`, placed in degree `0`, into degrees `≥ 0`, then it sends every bounded object
concentrated in degrees `≥ a` into degrees `≥ a`; if it sends them into degrees `≤ N`, it sends
a bounded object concentrated in degrees `≤ b` into degrees `≤ b + N`. Both follow by
dévissage along the truncation triangles `τ_{< b} E ⟶ E ⟶ Hᵇ(E)[-b] ⟶`.

For the derived direct image `Rf_*` the first hypothesis always holds, and the second one is the
uniform vanishing `UDV(f, Λ; N)` of the higher direct images above `N`
(`definition-cohomological-dimension--2`); this is the bound
`Rf_* D^{≤ t} ⊆ D^{≤ t + N}` used in `proposition-open-direct-image-preserves-finite--1`.

## Main results

- `DerivedCategory.isGE_obj_of_isGE_of_isLE`
- `DerivedCategory.isLE_obj_of_isGE_of_isLE`
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (G : DerivedCategory C ⥤ DerivedCategory D) [G.CommShift ℤ] [G.IsTriangulated]

omit [G.IsTriangulated] in
/-- The image under `G` of the third term `Hᵇ(E)[-b]` of the truncation triangle at `b` of an
object `E` with `E ≤ b`, as the shift of the image of an object placed in degree `0`. -/
private lemma exists_iso_shift_single_obj₃ (E : DerivedCategory C) (b : ℤ) [E.IsLE b] :
    ∃ X : C, Nonempty (G.obj ((TStructure.t.triangleLTGE b).obj E).obj₃ ≅
      (G.obj ((singleFunctor C 0).obj X))⟦-b⟧) := by
  have : ((TStructure.t.triangleLTGE b).obj E).obj₃.IsLE b :=
    inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj E) b)
  have : ((TStructure.t.triangleLTGE b).obj E).obj₃.IsGE b :=
    inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE b).obj E) b)
  obtain ⟨X, ⟨eX⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
    ((TStructure.t.triangleLTGE b).obj E).obj₃ b
  exact ⟨X, ⟨G.mapIso (eX ≪≫ (((singleFunctors C).shiftIso (-b) b 0 (by lia)).app X).symm) ≪≫
    (G.commShiftIso (-b)).app _⟩⟩

/-- **Lower bound on bounded objects.** If a triangulated functor `G : D(C) ⥤ D(D)` sends every
object of `C`, placed in degree `0`, into degrees `≥ 0`, then it sends an object concentrated in
degrees `[a, a + m - 1]` into degrees `≥ a`. -/
lemma isGE_obj_of_isGE_of_isLE
    (h : ∀ X : C, (G.obj ((singleFunctor C 0).obj X)).IsGE 0) (m : ℕ) :
    ∀ (a : ℤ) (E : DerivedCategory C), E.IsGE a → E.IsLE (a + m - 1) → (G.obj E).IsGE a := by
  induction m with
  | zero =>
    intro a E _ _
    have : E.IsLE (a - 1) := by simpa using ‹E.IsLE (a + ↑(0 : ℕ) - 1)›
    have hE := G.map_isZero (TStructure.t.isZero E (a - 1) a (by lia))
    exact TStructure.t.isGE_of_isZero hE a
  | succ m ih =>
    intro a E _ _
    set b : ℤ := a + m
    let T := (TStructure.t.triangleLTGE b).obj E
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b E
    have : E.IsLE b := TStructure.t.isLE_of_le E (a + ↑(m + 1) - 1) _ (by lia)
    obtain ⟨X, ⟨eX⟩⟩ := exists_iso_shift_single_obj₃ G E b
    have h₃ : (G.obj T.obj₃).IsGE a := by
      have := h X
      have : ((G.obj ((singleFunctor C 0).obj X))⟦-b⟧).IsGE b :=
        TStructure.t.isGE_shift _ 0 (-b) b (by lia)
      have : (G.obj T.obj₃).IsGE b := TStructure.t.isGE_of_iso eX.symm b
      exact TStructure.t.isGE_of_ge _ a b (by lia)
    have h₁ : (G.obj T.obj₁).IsGE a :=
      ih a T.obj₁ (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj E) a))
        (TStructure.t.isLE_truncLT_obj _ _ _ (by lia))
    exact TStructure.t.isGE₂ _ (G.map_distinguished _ hT) a h₁ h₃

/-- **Upper bound on bounded objects.** If a triangulated functor `G : D(C) ⥤ D(D)` sends every
object of `C`, placed in degree `0`, into degrees `≤ N`, then it sends an object concentrated in
degrees `[a, a + m - 1]` into degrees `≤ a + m - 1 + N`. -/
lemma isLE_obj_of_isGE_of_isLE (N : ℤ)
    (h : ∀ X : C, (G.obj ((singleFunctor C 0).obj X)).IsLE N) (m : ℕ) :
    ∀ (a : ℤ) (E : DerivedCategory C), E.IsGE a → E.IsLE (a + m - 1) →
      (G.obj E).IsLE (a + m - 1 + N) := by
  induction m with
  | zero =>
    intro a E _ _
    have : E.IsLE (a - 1) := by simpa using ‹E.IsLE (a + ↑(0 : ℕ) - 1)›
    have hE := G.map_isZero (TStructure.t.isZero E (a - 1) a (by lia))
    exact TStructure.t.isLE_of_isZero hE _
  | succ m ih =>
    intro a E _ _
    set b : ℤ := a + m
    let T := (TStructure.t.triangleLTGE b).obj E
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b E
    have : E.IsLE b := TStructure.t.isLE_of_le E (a + ↑(m + 1) - 1) _ (by lia)
    obtain ⟨X, ⟨eX⟩⟩ := exists_iso_shift_single_obj₃ G E b
    have h₃ : (G.obj T.obj₃).IsLE (b + N) := by
      have := h X
      have : ((G.obj ((singleFunctor C 0).obj X))⟦-b⟧).IsLE (b + N) :=
        TStructure.t.isLE_shift _ N (-b) (b + N) (by lia)
      exact TStructure.t.isLE_of_iso eX.symm _
    have h₁ : (G.obj T.obj₁).IsLE (b + N) := by
      have := ih a T.obj₁
        (inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj E) a))
        (TStructure.t.isLE_truncLT_obj _ _ _ (by lia))
      exact TStructure.t.isLE_of_le _ (a + m - 1 + N) _ (by lia)
    have : (G.obj E).IsLE (b + N) := TStructure.t.isLE₂ _ (G.map_distinguished _ hT) (b + N) h₁ h₃
    exact TStructure.t.isLE_of_le _ (b + N) _ (by lia)

/-- If a triangulated functor `G : D(C) ⥤ D(D)` sends every object of `C`, placed in degree `0`,
into degrees `≥ 0`, then it sends a bounded object concentrated in degrees `≥ a` into degrees
`≥ a`. -/
lemma isGE_obj_of_bounded (h : ∀ X : C, (G.obj ((singleFunctor C 0).obj X)).IsGE 0) (a b : ℤ)
    (E : DerivedCategory C) [E.IsGE a] [E.IsLE b] : (G.obj E).IsGE a := by
  have : E.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le E b _ (by lia)
  exact isGE_obj_of_isGE_of_isLE G h (b - a + 1).toNat a E inferInstance this

/-- If a triangulated functor `G : D(C) ⥤ D(D)` sends every object of `C`, placed in degree `0`,
into degrees `≤ N`, then it sends a bounded object concentrated in degrees `≤ b` into degrees
`≤ b + N`. -/
lemma isLE_obj_of_bounded (N : ℤ) (h : ∀ X : C, (G.obj ((singleFunctor C 0).obj X)).IsLE N)
    (a b : ℤ) (E : DerivedCategory C) [E.IsGE a] [E.IsLE b] : (G.obj E).IsLE (b + N) := by
  by_cases hab : a ≤ b
  · have : E.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le E b _ (by lia)
    have := isLE_obj_of_isGE_of_isLE G N h (b - a + 1).toNat a E inferInstance this
    exact TStructure.t.isLE_of_le _ (a + ↑(b - a + 1).toNat - 1 + N) _ (by lia)
  · have : E.IsLE (a - 1) := TStructure.t.isLE_of_le E b _ (by lia)
    have hE := G.map_isZero (TStructure.t.isZero E (a - 1) a (by lia))
    exact TStructure.t.isLE_of_isZero hE _

end DerivedCategory

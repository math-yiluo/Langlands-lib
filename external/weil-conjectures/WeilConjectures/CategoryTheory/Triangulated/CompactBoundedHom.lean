/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.CompactObjExtension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Compact objects with bounded morphisms

In a preadditive category, an object `s` is compact (`BrownRepresentability.IsCompactObj`) if
every morphism from `s` to a coproduct is a finite sum of morphisms through the summands. We show:

* compact objects are stable under retracts and, in a pretriangulated category, under extensions
  (`CategoryTheory.BrownRepresentability.IsCompactObj.of_distTriang`): this is the four lemma for
  the comparison of `⨁ⱼ Hom(-, Yⱼ)` with `Hom(-, ∐ⱼ Yⱼ)`, the latter map being always injective;
* compactness is transported along a left adjoint whose right adjoint preserves coproducts
  (`CategoryTheory.BrownRepresentability.IsCompactObj.of_adjunction`).

In a derived category, an object `s` *has bounded morphisms*
(`DerivedCategory.HasBoundedHom`) if `Hom(s, G) = 0` for all `G` in degrees `≤ n`, for some `n`.
The objects which are compact and have bounded morphisms form a triangulated subcategory stable
under retracts (`DerivedCategory.compactBoundedHom`), and the property is transported along left
adjoints whose right adjoints preserve coproducts and have bounded amplitude
(`DerivedCategory.compactBoundedHom_of_adjunction`).

These are the closure properties used in blueprint `proposition-compactness-finite-coefficients`:
the compact objects of a triangulated category form a thick subcategory.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Pretriangulated Category Preadditive ZeroObject

namespace CategoryTheory.BrownRepresentability

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A retract of a compact object is compact. -/
lemma IsCompactObj.of_retract {s s' : C} (hs : IsCompactObj s') (h : Retract s s') :
    IsCompactObj s := by
  intro J X c hc f
  obtain ⟨S, g, hg⟩ := hs c hc (h.r ≫ f)
  refine ⟨S, fun j ↦ h.i ≫ g j, ?_⟩
  rw [← id_comp f, ← h.retract, assoc, hg, comp_sum]
  simp only [assoc]

/-- Compactness is transported along a left adjoint whose right adjoint preserves coproducts. -/
lemma IsCompactObj.of_adjunction {D : Type u'} [Category.{v} D] [Preadditive D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) [F.Additive]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G] {s : C} (hs : IsCompactObj s) :
    IsCompactObj (F.obj s) := by
  intro J X c hc f
  obtain ⟨S, g, hg⟩ := hs _ (isColimitCofanMkObjOfIsColimit G X c.inj
    (hc.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp)))) (adj.homEquiv _ _ f)
  refine ⟨S, fun j ↦ (adj.homEquiv _ _).symm (g j), ?_⟩
  rw [← (adj.homEquiv _ _).symm_apply_apply f, hg]
  simp [Adjunction.homEquiv_counit, Functor.map_sum, Preadditive.sum_comp]

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

end CategoryTheory.BrownRepresentability

namespace DerivedCategory

open TStructure (t)
open BrownRepresentability

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]

/-- An object `s` of `D(A)` *has bounded morphisms* if there is `n` such that `Hom(s, G) = 0`
for every object `G` in degrees `≤ n`. -/
def HasBoundedHom (s : DerivedCategory A) : Prop :=
  ∃ n : ℤ, ∀ G : DerivedCategory A, G.IsLE n → ∀ f : s ⟶ G, f = 0

variable (A) in
/-- The objects of `D(A)` which are compact and have bounded morphisms. -/
def compactBoundedHom : ObjectProperty (DerivedCategory A) :=
  fun s ↦ IsCompactObj s ∧ HasBoundedHom s

instance : (compactBoundedHom A).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨h.1.of_iso e.symm, by
    obtain ⟨n, hn⟩ := h.2
    exact ⟨n, fun G hG f ↦ by rw [← cancel_epi e.hom, comp_zero]; exact hn G hG _⟩⟩

instance : (compactBoundedHom A).IsStableUnderRetracts where
  of_retract h hY := ⟨hY.1.of_retract h, by
    obtain ⟨n, hn⟩ := hY.2
    exact ⟨n, fun G hG f ↦ by rw [← id_comp f, ← h.retract, assoc, hn G hG (h.r ≫ f), comp_zero]⟩⟩

instance : (compactBoundedHom A).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun _ _ _ _ _ ↦ ⟨∅, fun _ ↦ 0, (isZero_zero _).eq_of_src _ _⟩,
    ⟨0, fun _ _ _ ↦ (isZero_zero _).eq_of_src _ _⟩⟩
  isStableUnderShiftBy k := ⟨fun s ⟨hs, n, hn⟩ ↦ ⟨hs.shift k, n - k, fun G hG f ↦ by
    let adj := (shiftEquiv' (DerivedCategory A) k (-k) (by simp)).toAdjunction
    have : (G⟦-k⟧).IsLE n := t.isLE_shift G (n - k) (-k) n (by lia)
    rw [← (adj.homEquiv _ _).symm_apply_apply f, hn _ this (adj.homEquiv _ _ f)]
    simp [Adjunction.homEquiv_counit]⟩⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT ⟨h₁, n₁, hn₁⟩ ⟨h₃, n₃, hn₃⟩ ↦
    ⟨h₁.of_distTriang T hT h₃, min n₁ n₃, fun G hG f ↦ by
      have := hG
      have h₁' : T.mor₁ ≫ f = 0 := hn₁ G (t.isLE_of_le G (min n₁ n₃) n₁ (min_le_left _ _)) _
      obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₂ _ hT f h₁'
      rw [hn₃ G (t.isLE_of_le G (min n₁ n₃) n₃ (min_le_right _ _)) g, comp_zero]⟩

/-- The property of being compact with bounded morphisms is transported along a left adjoint `F`
whose right adjoint `G` preserves coproducts and sends objects in degrees `≤ n` into degrees
`≤ n + c` for some `c`. -/
lemma compactBoundedHom_of_adjunction {B : Type u'} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{v} B] {F : DerivedCategory A ⥤ DerivedCategory B}
    {G : DerivedCategory B ⥤ DerivedCategory A} (adj : F ⊣ G) [F.Additive]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G] (c : ℤ)
    (hG : ∀ (Y : DerivedCategory B) (n : ℤ), Y.IsLE n → (G.obj Y).IsLE (n + c))
    {s : DerivedCategory A} (hs : compactBoundedHom A s) : compactBoundedHom B (F.obj s) := by
  obtain ⟨hs, n, hn⟩ := hs
  refine ⟨hs.of_adjunction adj, n - c, fun Y hY f ↦ ?_⟩
  have := hn _ (by simpa using hG Y (n - c) hY) (adj.homEquiv _ _ f)
  rw [← (adj.homEquiv _ _).symm_apply_apply f, this]
  simp [Adjunction.homEquiv_counit]

end DerivedCategory

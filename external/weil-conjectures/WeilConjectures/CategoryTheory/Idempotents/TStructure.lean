/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian

/-!
# The t-structure on the Karoubi envelope

Let `t` be a t-structure on a pretriangulated category `C`. The closures under retracts of the
images of `t.le n` and `t.ge n` form a t-structure `t.karoubi` on the Karoubi envelope
`Karoubi C`; the truncation triangle of `(K, e)` is the image of the idempotent endomorphism of
the truncation triangle of `K` induced by `e`.

## Main definitions

- `CategoryTheory.Triangulated.TStructure.karoubi`: the t-structure on `Karoubi C`.
- `CategoryTheory.Triangulated.TStructure.karoubiHeartEquivalence`: the heart of `t.karoubi` is
  canonically equivalent to the Karoubi envelope of the heart of `t`.

## Blueprint nodes formalised in Mathlib

Several blueprint nodes of the t-structure and Karoubi-envelope argument are Mathlib
definitions and instances:

- `def-weil-t-structure` (t-structures, their hearts, boundedness, truncation functors and
  truncation triangles) is `CategoryTheory.Triangulated.TStructure`, with
  `CategoryTheory.Triangulated.TStructure.heart`, `CategoryTheory.Triangulated.TStructure.bounded`,
  `CategoryTheory.Triangulated.TStructure.truncLE`, `CategoryTheory.Triangulated.TStructure.truncGE`
  and `CategoryTheory.Triangulated.TStructure.triangleLEGE_distinguished`.
- `def-weil-derived-cohomology-sheaves` (the cohomology sheaves `𝓗ʳ(K)` of a complex of sheaves of
  modules for the standard t-structure) is `DerivedCategory.homologyFunctor` applied to the
  derived category of a category of sheaves of modules, the standard t-structure being
  `DerivedCategory.TStructure.t`; this standard t-structure on the derived category of an
  abelian category is blueprint `def-sbc-standard-tstructure-derived-category`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Idempotents

namespace Triangulated.TStructure

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- The closure under retracts of the image in `Karoubi C` of a property of objects of `C`. -/
def karoubiProp (P : ObjectProperty C) : ObjectProperty (Karoubi C) :=
  fun Q ↦ ∃ X, P X ∧ Nonempty (Retract Q ((toKaroubi C).obj X))

instance (P : ObjectProperty C) : (karoubiProp P).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨X, hX, ⟨r⟩⟩ ↦ ⟨X, hX, ⟨(Retract.ofIso e.symm).trans r⟩⟩

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma karoubiProp_toKaroubi_obj {P : ObjectProperty C} {X : C} (hX : P X) :
    karoubiProp P ((toKaroubi C).obj X) :=
  ⟨X, hX, ⟨Retract.refl _⟩⟩

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma karoubiProp_monotone {P P' : ObjectProperty C} (h : P ≤ P') :
    karoubiProp P ≤ karoubiProp P' :=
  fun _ ⟨X, hX, r⟩ ↦ ⟨X, h _ hX, r⟩

/-- A morphism from a retract of the image of an object `≤ n` to a retract of the image of an
object `≥ n + 1` is zero. -/
lemma karoubi_zero {A B : Karoubi C} (f : A ⟶ B) (n : ℤ) (hA : karoubiProp (t.le n) A)
    (hB : karoubiProp (t.ge (n + 1)) B) : f = 0 := by
  obtain ⟨X, hX, ⟨rA⟩⟩ := hA
  obtain ⟨Y, hY, ⟨rB⟩⟩ := hB
  have : t.IsLE X n := ⟨hX⟩
  have : t.IsGE Y (n + 1) := ⟨hY⟩
  have h : rA.r ≫ f ≫ rB.i = 0 := by
    rw [← (toKaroubi C).map_preimage (rA.r ≫ f ≫ rB.i),
      t.zero ((toKaroubi C).preimage (rA.r ≫ f ≫ rB.i)) n (n + 1) (by lia), Functor.map_zero]
  calc f = rA.i ≫ (rA.r ≫ f ≫ rB.i) ≫ rB.r := by simp
    _ = 0 := by rw [h, zero_comp, comp_zero]

/-- The t-structure on the Karoubi envelope whose subcategories `≤ n` and `≥ n` are the
closures under retracts of the images of `t.le n` and `t.ge n`. -/
noncomputable def karoubi : TStructure (Karoubi C) where
  le n := karoubiProp (t.le n)
  ge n := karoubiProp (t.ge n)
  le_shift n a n' h Q := fun ⟨X, hX, ⟨r⟩⟩ ↦ ⟨X⟦a⟧, t.le_shift n a n' h X hX,
    ⟨(r.map (shiftFunctor _ a)).trans (Retract.ofIso (((toKaroubi C).commShiftIso a).symm.app X))⟩⟩
  ge_shift n a n' h Q := fun ⟨X, hX, ⟨r⟩⟩ ↦ ⟨X⟦a⟧, t.ge_shift n a n' h X hX,
    ⟨(r.map (shiftFunctor _ a)).trans (Retract.ofIso (((toKaroubi C).commShiftIso a).symm.app X))⟩⟩
  zero' := fun ⦃_ _⦄ f hX hY ↦ t.karoubi_zero f 0 hX hY
  le_zero_le := karoubiProp_monotone t.le_zero_le
  ge_one_le := karoubiProp_monotone t.ge_one_le
  exists_triangle_zero_one Q := by
    let T := (t.triangleLEGE 0 1 rfl).obj Q.X
    let E : T ⟶ T := (t.triangleLEGE 0 1 rfl).map Q.p
    have hE : E ≫ E = E := by rw [← Functor.map_comp, Q.idem]
    have hT := Karoubi.triangleOfIdem_distinguished T (t.triangleLEGE_distinguished 0 1 rfl Q.X)
      E hE
    refine ⟨_, _, ⟨(t.truncLE 0).obj Q.X, t.le_of_isLE ((t.truncLE 0).obj Q.X) 0,
      ⟨Karoubi.retract _⟩⟩, ⟨(t.truncGE 1).obj Q.X, t.ge_of_isGE ((t.truncGE 1).obj Q.X) 1,
      ⟨Karoubi.retract _⟩⟩, (Karoubi.triangleOfIdem T E hE).mor₁,
      (Karoubi.triangleOfIdem T E hE).mor₂, (Karoubi.triangleOfIdem T E hE).mor₃, ?_⟩
    exact hT

section Heart

/-- A retract `Q` of `X` in the Karoubi envelope is isomorphic to `(X, r ≫ i)`. -/
def _root_.CategoryTheory.Idempotents.Karoubi.isoOfRetract {Q : Karoubi C} {X : C}
    (r : Retract Q ((toKaroubi C).obj X)) :
    Q ≅ ⟨X, (r.r ≫ r.i).f, by rw [← Karoubi.comp_f, assoc, r.retract_assoc]⟩ where
  hom := ⟨r.i.f, by
    have h1 := congrArg Karoubi.Hom.f (r.retract_assoc r.i)
    simp only [Karoubi.comp_f] at h1
    dsimp
    rw [h1, Karoubi.p_comp]⟩
  inv := ⟨r.r.f, by
    have h1 : r.r ≫ r.i ≫ r.r = r.r := by rw [r.retract, comp_id]
    have h2 := congrArg Karoubi.Hom.f h1
    simp only [Karoubi.comp_f] at h2
    dsimp
    rw [Karoubi.comp_p, assoc, h2]⟩
  hom_inv_id := by ext; exact congrArg Karoubi.Hom.f r.retract
  inv_hom_id := by ext; rfl

/-- If `e = r ≫ i` with `i ≫ r = 𝟙`, then `(X, e)` is isomorphic to the image of `A`. -/
def _root_.CategoryTheory.Idempotents.Karoubi.isoToKaroubiOfSplit {X A : C} {e : X ⟶ X}
    (he : e ≫ e = e) (i : A ⟶ X) (r : X ⟶ A) (hir : i ≫ r = 𝟙 A) (hri : r ≫ i = e) :
    (⟨X, e, he⟩ : Karoubi C) ≅ (toKaroubi C).obj A where
  hom := ⟨r, by dsimp; rw [← hri]; simp only [assoc, comp_id, hir]⟩
  inv := ⟨i, by dsimp; rw [id_comp, ← hri, ← assoc, hir, id_comp]⟩
  hom_inv_id := by ext; exact hri
  inv_hom_id := by ext; exact hir

variable [IsTriangulated C]

/-- The inclusion of the heart of `t` into the heart of `t.karoubi`. -/
noncomputable def heartToKaroubi : t.heart.FullSubcategory ⥤ t.karoubi.heart.FullSubcategory :=
  t.karoubi.heart.lift (t.heart.ι ⋙ toKaroubi C) fun A ↦
    ⟨karoubiProp_toKaroubi_obj A.property.1, karoubiProp_toKaroubi_obj A.property.2⟩

instance : (t.heartToKaroubi).Full where
  map_surjective {A B} f :=
    ⟨ObjectProperty.homMk f.hom.f, by ext; rfl⟩

instance : (t.heartToKaroubi).Faithful where
  map_injective {A B} f g h := by
    ext
    exact congrArg (fun φ ↦ φ.hom.f) h

instance : (t.heartToKaroubi).EssSurj where
  mem_essImage P := by
    obtain ⟨⟨X, hX, ⟨r⟩⟩, hP₂⟩ := P.property
    have : t.IsLE X 0 := ⟨hX⟩
    let e₀ : X ⟶ X := (r.r ≫ r.i).f
    have he₀ : e₀ ≫ e₀ = e₀ := by
      simp only [e₀, ← Karoubi.comp_f, assoc, r.retract_assoc]
    let eP := Karoubi.isoOfRetract r
    -- the truncation triangle of `X` at `-1`, with the idempotent induced by `e₀`
    let T := (t.triangleLEGE (-1) 0 (by lia)).obj X
    let E : T ⟶ T := (t.triangleLEGE (-1) 0 (by lia)).map e₀
    have hE : E ≫ E = E := by rw [← Functor.map_comp, he₀]
    have hT := Karoubi.triangleOfIdem_distinguished T
      (t.triangleLEGE_distinguished (-1) 0 (by lia) X) E hE
    -- its first morphism vanishes, so that `τ_{≤ -1} e₀ = 0`
    have h₁ : (Karoubi.triangleOfIdem T E hE).mor₁ = 0 :=
      t.karoubi_zero _ (-1) ⟨_, t.le_of_isLE ((t.truncLE (-1)).obj X) (-1), ⟨Karoubi.retract _⟩⟩
        ((karoubiProp (t.ge 0)).prop_of_iso eP hP₂)
    have h₁' : (t.truncLE (-1)).map e₀ = 0 := t.to_truncLE_obj_ext (by
      have := congrArg Karoubi.Hom.f h₁
      change (t.truncLEι (-1)).app X ≫ e₀ = 0 at this
      rw [zero_comp, (t.truncLEι (-1)).naturality e₀]
      exact this)
    have hZ : IsZero (Karoubi.triangleOfIdem T E hE).obj₁ := by
      rw [IsZero.iff_id_eq_zero]
      ext
      change (t.truncLE (-1)).map e₀ = 0
      exact h₁'
    have hiso := (Triangle.isZero₁_iff_isIso₂ _ hT).1 hZ
    -- `τ_{≥ 0} X` lies in the heart, and `τ_{≥ 0} e₀` splits there
    have hA : t.heart ((t.truncGE 0).obj X) := (t.mem_heart_iff _).2 ⟨inferInstance, inferInstance⟩
    let := t.hasHeartFullSubcategory
    have hsplit := (Idempotents.isIdempotentComplete_iff_isSplit.1
      (t.isIdempotentComplete_heart t.heart.FullSubcategory)) ⟨_, hA⟩
      (ObjectProperty.homMk E.hom₃) (by ext; exact Karoubi.idem_hom₃ T E hE)
    obtain ⟨A, i, r', hir, hri⟩ := hsplit
    let eA := Karoubi.isoToKaroubiOfSplit (Karoubi.idem_hom₃ T E hE) i.hom r'.hom
      (by simpa using congrArg (fun φ ↦ φ.hom) hir)
      (by simpa using congrArg (fun φ ↦ φ.hom) hri)
    exact ⟨A, ⟨t.karoubi.heart.fullyFaithfulι.preimageIso
      ((eP ≪≫ asIso (Karoubi.triangleOfIdem T E hE).mor₂ ≪≫ eA).symm)⟩⟩

/-- The canonical equivalence between the heart of the t-structure on the Karoubi envelope and
the Karoubi envelope of the heart. It is the inverse of
the equivalence `t.heartToKaroubi` from the heart of `C` (idempotent complete, since it is
abelian) followed by the equivalence of the heart with its Karoubi envelope. -/
noncomputable def karoubiHeartEquivalence :
    t.karoubi.heart.FullSubcategory ≌ Karoubi t.heart.FullSubcategory :=
  letI := t.hasHeartFullSubcategory
  haveI := t.isIdempotentComplete_heart t.heart.FullSubcategory
  haveI : t.heartToKaroubi.IsEquivalence := { }
  t.heartToKaroubi.asEquivalence.symm.trans (toKaroubiEquivalence _)

end Heart

/-- For a triangulated category with a bounded t-structure, the canonical functor into the
Karoubi envelope is an exact equivalence. -/
theorem isEquivalence_toKaroubi_and_isTriangulated_of_bounded [IsTriangulated C]
    (ht : ∀ X : C, t.bounded X) :
    (toKaroubi C).IsEquivalence ∧ (toKaroubi C).IsTriangulated :=
  ⟨t.isEquivalence_toKaroubi_of_bounded ht, inferInstance⟩

end Triangulated.TStructure

end CategoryTheory

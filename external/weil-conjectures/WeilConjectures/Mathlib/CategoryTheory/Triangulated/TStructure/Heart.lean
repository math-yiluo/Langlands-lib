/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The heart of a t-structure is abelian

Let `t` be a t-structure on a triangulated category `C`. Using that the subcategories `t.le n`
and `t.ge n` are closed under extensions (`CategoryTheory.Triangulated.TStructure.isLE₂` and
`CategoryTheory.Triangulated.TStructure.isGE₂`, from Mathlib), we show that the heart of `t` is
an abelian category ([BBD, Théorème 1.3.6]). Consequently the heart is idempotent complete.

## Main statements

- `CategoryTheory.Triangulated.TStructure.abelianHeart`: the heart is abelian.
- `CategoryTheory.Triangulated.TStructure.isIdempotentComplete_heart`: the heart is idempotent
  complete.

## References

* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*, 1.3][bbd-1982]
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

section Heart

variable [IsTriangulated C] (H : Type u') [Category.{v'} H] [Preadditive H] [t.Heart H]

omit [IsTriangulated C] in
variable {H} in
lemma ιHeart_hom_shift_eq_zero {X Y : H} {n : ℤ}
    (f : t.ιHeart.obj X ⟶ (t.ιHeart.obj Y)⟦n⟧) (hn : n < 0) : f = 0 :=
  have := t.isGE_shift (t.ιHeart.obj Y) 0 n (-n) (by lia)
  t.zero f 0 (-n) (by lia)

omit [IsTriangulated C] in
variable {H} in
lemma exists_ιHeart_obj_iso {X : C} (hX : t.heart X) :
    ∃ (Y : H), Nonempty (t.ιHeart.obj Y ≅ X) := by
  rw [← t.essImage_ιHeart H] at hX
  exact hX

lemma admissibleMorphism_ιHeart_eq_top :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) = ⊤ := by
  ext X₁ X₂ f₁
  simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  have h₁ : t.IsLE X₃ 0 := t.isLE₂ _ (rot_of_distTriang _ hT) 0
    (inferInstanceAs (t.IsLE (t.ιHeart.obj X₂) 0))
    (by
      have := t.isLE_shift (t.ιHeart.obj X₁) 0 1 (-1) (by lia)
      exact t.isLE_of_le ((t.ιHeart.obj X₁)⟦(1 : ℤ)⟧) (-1) 0)
  have h₂ : t.IsGE X₃ (-1) := t.isGE₂ _ (rot_of_distTriang _ hT) (-1)
    (by exact t.isGE_of_ge (t.ιHeart.obj X₂) (-1) 0)
    (by exact t.isGE_shift (t.ιHeart.obj X₁) 0 1 (-1) (by lia))
  have hK : t.heart (((t.truncLE (-1)).obj X₃)⟦(-1 : ℤ)⟧) := by
    rw [mem_heart_iff]
    exact ⟨t.isLE_shift _ (-1) (-1) 0 (by lia), t.isGE_shift _ (-1) (-1) 0 (by lia)⟩
  have hQ : t.heart ((t.truncGE 0).obj X₃) := by
    rw [mem_heart_iff]
    constructor <;> infer_instance
  obtain ⟨K, ⟨eK⟩⟩ := t.exists_ιHeart_obj_iso (H := H) hK
  obtain ⟨Q, ⟨eQ⟩⟩ := t.exists_ιHeart_obj_iso (H := H) hQ
  have hT' := t.triangleLEGE_distinguished (-1) 0 (by lia) X₃
  let e₁ : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLE (-1)).obj X₃ :=
    (shiftFunctor C (1 : ℤ)).mapIso eK ≪≫ (shiftFunctorCompIsoId C (-1) 1 (by lia)).app _
  refine ⟨K, Q, e₁.hom ≫ (t.truncLEι (-1)).app X₃, (t.truncGEπ 0).app X₃ ≫ eQ.inv,
    eQ.hom ≫ (t.truncGEδLE (-1) 0 (by lia)).app X₃ ≫ e₁.inv⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hT' _ (Triangle.isoMk _ _ e₁ (Iso.refl _) eQ ?_ ?_ ?_)⟩
  · dsimp; simp
  · dsimp; simp
  · dsimp; simp [← Functor.map_comp]

omit [IsTriangulated C] in
variable {H} in
lemma heart_biprod (X Y : H) : t.heart (t.ιHeart.obj X ⊞ t.ιHeart.obj Y) := by
  have hT := binaryBiproductTriangle_distinguished (t.ιHeart.obj X) (t.ιHeart.obj Y)
  rw [mem_heart_iff]
  exact ⟨t.isLE₂ _ hT 0 (inferInstanceAs (t.IsLE (t.ιHeart.obj X) 0))
    (inferInstanceAs (t.IsLE (t.ιHeart.obj Y) 0)),
    t.isGE₂ _ hT 0 (inferInstanceAs (t.IsGE (t.ιHeart.obj X) 0))
    (inferInstanceAs (t.IsGE (t.ιHeart.obj Y) 0))⟩

omit [IsTriangulated C] in
include t in
lemma hasBinaryBiproducts_heart : HasBinaryBiproducts H where
  has_binary_biproduct X Y := by
    obtain ⟨Z, ⟨e⟩⟩ := t.exists_ιHeart_obj_iso (H := H) (t.heart_biprod X Y)
    exact HasBinaryBiproduct.mk
      { bicone :=
          { pt := Z
            fst := (t.ιHeart (H := H)).preimage (e.hom ≫ biprod.fst)
            snd := (t.ιHeart (H := H)).preimage (e.hom ≫ biprod.snd)
            inl := (t.ιHeart (H := H)).preimage (biprod.inl ≫ e.inv)
            inr := (t.ιHeart (H := H)).preimage (biprod.inr ≫ e.inv)
            inl_fst := (t.ιHeart (H := H)).map_injective (by simp)
            inl_snd := (t.ιHeart (H := H)).map_injective (by simp)
            inr_fst := (t.ιHeart (H := H)).map_injective (by simp)
            inr_snd := (t.ιHeart (H := H)).map_injective (by simp) }
        isBilimit := isBinaryBilimitOfTotal _ ((t.ιHeart (H := H)).map_injective (by
          simp only [Functor.map_add, Functor.map_comp, Functor.map_preimage, Functor.map_id]
          have : e.hom ≫ (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ e.inv = 𝟙 _ := by
            rw [biprod.total, id_comp, Iso.hom_inv_id]
          simpa only [Preadditive.comp_add, Preadditive.add_comp, assoc] using this)) }

omit [IsTriangulated C] in
include t in
lemma hasZeroObject_heart : HasZeroObject H := by
  obtain ⟨Z, ⟨e⟩⟩ := t.exists_ιHeart_obj_iso (H := H) (X := 0) (by
    rw [mem_heart_iff]; constructor <;> infer_instance)
  refine ⟨Z, ?_⟩
  rw [IsZero.iff_id_eq_zero]
  exact (t.ιHeart (H := H)).map_injective
    (by rw [Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero];
        exact IsZero.of_iso (isZero_zero C) e)

omit [IsTriangulated C] in
include t in
lemma hasFiniteProducts_heart : HasFiniteProducts H :=
  have := t.hasBinaryBiproducts_heart H
  have := t.hasZeroObject_heart H
  hasFiniteProducts_of_has_binary_and_terminal

/-- Blueprint `lemma-perverse-sheaves-curve--1`: the heart of a t-structure on a triangulated
category is an abelian category ([BBD, Théorème 1.3.6]). -/
@[instance_reducible]
noncomputable def abelianHeart : Abelian H :=
  have := t.hasFiniteProducts_heart H
  AbelianSubcategory.abelian t.ιHeart (fun _ _ _ f hn ↦ t.ιHeart_hom_shift_eq_zero f hn)
    (t.admissibleMorphism_ιHeart_eq_top H)

include t in
/-- Blueprint `lemma-perverse-sheaves-curve--1`: the heart of a t-structure is idempotent complete,
since it is abelian. -/
theorem isIdempotentComplete_heart : IsIdempotentComplete H := by
  let := t.abelianHeart H
  rw [Idempotents.isIdempotentComplete_iff_idempotents_have_kernels]
  intro X p _
  infer_instance
end Heart

end CategoryTheory.Triangulated.TStructure

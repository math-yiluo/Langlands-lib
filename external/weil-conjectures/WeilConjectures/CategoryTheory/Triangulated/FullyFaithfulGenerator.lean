/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Full faithfulness of triangulated functors on generated subcategories

Let `F : C ⥤ D` be a triangulated functor between pretriangulated categories. For objects `X`
and `Y` of `C`, consider the condition `F.HomBijective X Y` that `F` induces a bijection
`(X ⟶ Y) ≃ (F X ⟶ F Y)`, and its shifted version `F.HomBijectiveShifts X Y`, which asks this
for all the shifts `X⟦a⟧`, `Y⟦b⟧`. By the five lemma applied to the long exact sequences of
`Hom` groups attached to a distinguished triangle, for fixed `X` the objects `Y` with
`F.HomBijectiveShifts X Y` form a triangulated subcategory of `C`, and similarly for fixed `Y`.

Consequently, if every object of `C` lies in every triangulated subcategory containing an
object `G`, and `F` is bijective on the morphisms `G⟦a⟧ ⟶ G⟦b⟧`, then `F` is fully faithful
(`CategoryTheory.Functor.fullyFaithfulOfGenerator`).

## Main statements

- `CategoryTheory.Functor.homBijective_obj₂_of_triangle`,
  `CategoryTheory.Functor.homBijective_obj₂_of_triangle'`: the five lemmas.
- `CategoryTheory.Functor.isTriangulated_homBijectiveShiftsRight`,
  `CategoryTheory.Functor.isTriangulated_homBijectiveShiftsLeft`: the triangulated
  subcategories.
- `CategoryTheory.Functor.fullyFaithfulOfGenerator`: full faithfulness from a generator.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Preadditive ZeroObject

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- The functor `F` induces a bijection `(X ⟶ Y) ≃ (F X ⟶ F Y)`. -/
def HomBijective (X Y : C) : Prop :=
  Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))

variable {F}

lemma HomBijective.of_iso {X Y X' Y' : C} (h : F.HomBijective X Y) (e : X ≅ X') (e' : Y ≅ Y') :
    F.HomBijective X' Y' := by
  have h₁ : (F.map : (X' ⟶ Y') → (F.obj X' ⟶ F.obj Y')) =
      (fun g : F.obj X ⟶ F.obj Y ↦ F.map e.inv ≫ g ≫ F.map e'.hom) ∘
        (fun f : X ⟶ Y ↦ F.map f) ∘ (fun f : X' ⟶ Y' ↦ e.hom ≫ f ≫ e'.inv) := by
    ext f
    simp [← Functor.map_comp]
  have h₂ : Function.Bijective (fun f : X' ⟶ Y' ↦ e.hom ≫ f ≫ e'.inv) :=
    ((Iso.homCongr e.symm e'.symm).bijective)
  have h₃ : Function.Bijective (fun g : F.obj X ⟶ F.obj Y ↦ F.map e.inv ≫ g ≫ F.map e'.hom) :=
    ((Iso.homCongr (F.mapIso e) (F.mapIso e')).bijective)
  unfold HomBijective
  rw [h₁]
  exact h₃.comp (h.comp h₂)

/-- `F.HomBijective X Y` only depends on `X` up to isomorphism. -/
lemma HomBijective.of_iso_left {X Y X' : C} (h : F.HomBijective X Y) (e : X ≅ X') :
    F.HomBijective X' Y :=
  h.of_iso e (Iso.refl _)

/-- `F.HomBijective X Y` only depends on `Y` up to isomorphism. -/
lemma HomBijective.of_iso_right {X Y Y' : C} (h : F.HomBijective X Y) (e : Y ≅ Y') :
    F.HomBijective X Y' :=
  h.of_iso (Iso.refl _) e

section Zero

variable [Preadditive C] [Preadditive D]

lemma HomBijective.of_isZero_left {X Y : C} (hX : IsZero X) [F.PreservesZeroMorphisms] :
    F.HomBijective X Y :=
  ⟨fun _ _ _ ↦ hX.eq_of_src _ _, fun _ ↦ ⟨0, (F.map_isZero hX).eq_of_src _ _⟩⟩

lemma HomBijective.of_isZero_right {X Y : C} (hY : IsZero Y) [F.PreservesZeroMorphisms] :
    F.HomBijective X Y :=
  ⟨fun _ _ _ ↦ hY.eq_of_tgt _ _, fun _ ↦ ⟨0, (F.map_isZero hY).eq_of_tgt _ _⟩⟩

end Zero

section Biprod

variable [Preadditive C] [Preadditive D] [F.Additive] [HasBinaryBiproducts C]

/-- If `F` is bijective on the morphisms `X₁ ⟶ Y` and `X₂ ⟶ Y`, it is bijective on the morphisms
`X₁ ⊞ X₂ ⟶ Y`: a morphism `F (X₁ ⊞ X₂) ⟶ F Y` is determined by its restrictions along
`F inl` and `F inr`.
```
F X₁ --F inl--> F (X₁ ⊞ X₂) <--F inr-- F X₂
                     |
                     v
                    F Y
```
-/
lemma HomBijective.biprod_left {X₁ X₂ Y : C} (h₁ : F.HomBijective X₁ Y)
    (h₂ : F.HomBijective X₂ Y) : F.HomBijective (X₁ ⊞ X₂) Y := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine biprod.hom_ext' _ _ (h₁.1 ?_) (h₂.1 ?_) <;>
      simp only [F.map_comp] <;> exact congrArg (_ ≫ ·) hφψ
  · obtain ⟨φ₁, hφ₁⟩ := h₁.2 (F.map biprod.inl ≫ χ)
    obtain ⟨φ₂, hφ₂⟩ := h₂.2 (F.map biprod.inr ≫ χ)
    refine ⟨biprod.desc φ₁ φ₂, ?_⟩
    rw [biprod.desc_eq, F.map_add, F.map_comp, F.map_comp, hφ₁, hφ₂, ← Category.assoc,
      ← Category.assoc, ← F.map_comp, ← F.map_comp, ← Preadditive.add_comp, ← F.map_add,
      biprod.total, F.map_id, Category.id_comp]

/-- If `F` is bijective on the morphisms `X ⟶ Y₁` and `X ⟶ Y₂`, it is bijective on the morphisms
`X ⟶ Y₁ ⊞ Y₂`: a morphism `F X ⟶ F (Y₁ ⊞ Y₂)` is determined by its composites with
`F fst` and `F snd`.
```
                    F X
                     |
                     v
F Y₁ <--F fst-- F (Y₁ ⊞ Y₂) --F snd--> F Y₂
```
-/
lemma HomBijective.biprod_right {X Y₁ Y₂ : C} (h₁ : F.HomBijective X Y₁)
    (h₂ : F.HomBijective X Y₂) : F.HomBijective X (Y₁ ⊞ Y₂) := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine biprod.hom_ext _ _ (h₁.1 ?_) (h₂.1 ?_) <;>
      simp only [F.map_comp] <;> exact congrArg (· ≫ _) hφψ
  · obtain ⟨φ₁, hφ₁⟩ := h₁.2 (χ ≫ F.map biprod.fst)
    obtain ⟨φ₂, hφ₂⟩ := h₂.2 (χ ≫ F.map biprod.snd)
    refine ⟨biprod.lift φ₁ φ₂, ?_⟩
    rw [biprod.lift_eq, F.map_add, F.map_comp, F.map_comp, hφ₁, hφ₂, Category.assoc,
      Category.assoc, ← F.map_comp, ← F.map_comp, ← Preadditive.comp_add, ← F.map_add,
      biprod.total, F.map_id, Category.comp_id]

end Biprod

variable [HasShift C ℤ]

variable (F) in
/-- `F` induces bijections `(X⟦a⟧ ⟶ Y⟦b⟧) ≃ (F (X⟦a⟧) ⟶ F (Y⟦b⟧))` for all shifts. -/
def HomBijectiveShifts (X Y : C) : Prop :=
  ∀ a b : ℤ, F.HomBijective (X⟦a⟧) (Y⟦b⟧)

lemma HomBijectiveShifts.homBijective {X Y : C} (h : F.HomBijectiveShifts X Y) :
    F.HomBijective X Y :=
  (h 0 0).of_iso ((shiftFunctorZero C ℤ).app X) ((shiftFunctorZero C ℤ).app Y)

lemma HomBijectiveShifts.shift_left {X Y : C} (h : F.HomBijectiveShifts X Y) (c : ℤ) :
    F.HomBijectiveShifts (X⟦c⟧) Y := fun a b ↦
  (h (c + a) b).of_iso ((shiftFunctorAdd C c a).app X) (Iso.refl _)

lemma HomBijectiveShifts.shift_right {X Y : C} (h : F.HomBijectiveShifts X Y) (c : ℤ) :
    F.HomBijectiveShifts X (Y⟦c⟧) := fun a b ↦
  (h a (c + b)).of_iso (Iso.refl _) ((shiftFunctorAdd C c b).app Y)

section Shift

variable [HasShift D ℤ] [F.CommShift ℤ]

lemma HomBijective.shift {X Y : C} (h : F.HomBijective X Y) (c : ℤ) :
    F.HomBijective (X⟦c⟧) (Y⟦c⟧) := by
  have e : (fun f : X ⟶ Y ↦ F.map (f⟦c⟧')) = (fun g : F.obj X ⟶ F.obj Y ↦
      (F.commShiftIso c).hom.app X ≫ g⟦c⟧' ≫ (F.commShiftIso c).inv.app Y) ∘ F.map := by
    ext f
    simp
  have h₁ : Function.Bijective (fun g : F.obj X ⟶ F.obj Y ↦
      (F.commShiftIso c).hom.app X ≫ g⟦c⟧' ≫ (F.commShiftIso c).inv.app Y) :=
    (Iso.homCongr ((F.commShiftIso c).app X).symm ((F.commShiftIso c).app Y).symm).bijective.comp
      ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D c)).map_bijective _ _)
  have h₂ : Function.Bijective ((F.map : (X⟦c⟧ ⟶ Y⟦c⟧) → _) ∘ (shiftFunctor C c).map) := by
    change Function.Bijective (fun f : X ⟶ Y ↦ F.map (f⟦c⟧'))
    rw [e]
    exact h₁.comp h
  exact (Function.Bijective.of_comp_iff _
    ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C c)).map_bijective _ _)).1 h₂

/-- If `F` is bijective on the morphisms `X ⟶ Y⟦n⟧` for all `n`, it is bijective on the
morphisms `X⟦a⟧ ⟶ Y⟦b⟧` for all `a`, `b`. -/
lemma homBijectiveShifts_of_forall {X Y : C} (h : ∀ n : ℤ, F.HomBijective X (Y⟦n⟧)) :
    F.HomBijectiveShifts X Y := fun a b ↦
  ((h (b - a)).shift a).of_iso (Iso.refl _)
    ((shiftFunctorAdd' C (b - a) a b (by lia)).app Y).symm

end Shift

variable [HasZeroObject C]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

section Triangulated

variable [F.CommShift ℤ] [F.IsTriangulated]

/-- The five lemma for the covariant `Hom` sequence of a distinguished triangle
`T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧`: if `F` is bijective on the morphisms from `X` to `T₁` and `T₃`,
surjective on those to `T₃⟦-1⟧` and injective on those to `T₁⟦1⟧`, it is bijective on those
to `T₂`. -/
lemma homBijective_obj₂_of_triangle (X : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : F.HomBijective X T.obj₁) (h₃ : F.HomBijective X T.obj₃)
    (h₀ : Function.Surjective (F.map : (X ⟶ T.invRotate.obj₁) → _))
    (h₄ : Function.Injective (F.map : (X ⟶ T.obj₁⟦(1 : ℤ)⟧) → _)) :
    F.HomBijective X T.obj₂ := by
  have hFT := F.map_distinguished _ hT
  have hT' := inv_rot_of_distTriang _ hT
  have hFT' := F.map_distinguished _ hT'
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero]
    set z := x - y
    have hz : F.map z = 0 := by simp [z, hxy]
    have : z ≫ T.mor₂ = 0 := h₃.1 (by simp [hz])
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT z this
    have : F.map g ≫ (F.mapTriangle.obj T.invRotate).mor₂ = 0 := by
      change F.map g ≫ F.map T.mor₁ = 0
      rw [← F.map_comp, ← hg, hz]
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ _ hFT' (F.map g) this
    obtain ⟨h', rfl⟩ := h₀ h
    have : g = h' ≫ T.invRotate.mor₁ := h₁.1 (by rw [hh, F.map_comp]; rfl)
    rw [hg, this, assoc]
    change h' ≫ T.invRotate.mor₁ ≫ T.invRotate.mor₂ = 0
    rw [comp_distTriang_mor_zero₁₂ _ hT', comp_zero]
  · obtain ⟨c, hc⟩ := h₃.2 (y ≫ F.map T.mor₂)
    have : c ≫ T.mor₃ = 0 := h₄ (by
      rw [F.map_comp, hc, assoc, ← F.map_comp, comp_distTriang_mor_zero₂₃ _ hT,
        F.map_zero, comp_zero, F.map_zero])
    obtain ⟨b, rfl⟩ := Triangle.coyoneda_exact₃ T hT c this
    have : (y - F.map b) ≫ (F.mapTriangle.obj T).mor₂ = 0 := by
      change (y - F.map b) ≫ F.map T.mor₂ = 0
      rw [sub_comp, ← hc, F.map_comp, sub_self]
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ _ hFT _ this
    obtain ⟨a', rfl⟩ := h₁.2 a
    refine ⟨b + a' ≫ T.mor₁, ?_⟩
    rw [F.map_add, F.map_comp]
    rw [sub_eq_iff_eq_add'] at ha
    rw [ha]
    rfl

/-- The five lemma for the contravariant `Hom` sequence of a distinguished triangle
`T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧`: if `F` is bijective on the morphisms from `T₁` and `T₃` to `Y`,
surjective on those from `T₁⟦1⟧` and injective on those from `T₃⟦-1⟧`, it is bijective on
those from `T₂`. -/
lemma homBijective_obj₂_of_triangle' (Y : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : F.HomBijective T.obj₁ Y) (h₃ : F.HomBijective T.obj₃ Y)
    (h₀ : Function.Injective (F.map : (T.invRotate.obj₁ ⟶ Y) → _))
    (h₄ : Function.Surjective (F.map : (T.obj₁⟦(1 : ℤ)⟧ ⟶ Y) → _)) :
    F.HomBijective T.obj₂ Y := by
  have hFT := F.map_distinguished _ hT
  have hT' := inv_rot_of_distTriang _ hT
  have hFT' := F.map_distinguished _ hT'
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · rw [← sub_eq_zero]
    set z := x - y
    have hz : F.map z = 0 := by simp [z, hxy]
    have : T.mor₁ ≫ z = 0 := h₁.1 (by simp [hz])
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT z this
    have : (F.mapTriangle.obj T).mor₂ ≫ F.map g = 0 := by
      change F.map T.mor₂ ≫ F.map g = 0
      rw [← F.map_comp, ← hg, hz]
    obtain ⟨h, hh⟩ := Triangle.yoneda_exact₃ _ hFT (F.map g) this
    obtain ⟨h', hh'⟩ := h₄ ((F.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ h)
    have : g = T.mor₃ ≫ h' := h₃.1 (by
      rw [hh, F.map_comp, hh']
      exact assoc _ _ _)
    rw [hg, this, ← assoc, comp_distTriang_mor_zero₂₃ _ hT, zero_comp]
  · obtain ⟨a, ha⟩ := h₁.2 (F.map T.mor₁ ≫ y)
    have : T.invRotate.mor₁ ≫ a = 0 := h₀ (by
      rw [F.map_comp, ha, ← assoc, ← F.map_comp]
      change F.map (T.invRotate.mor₁ ≫ T.invRotate.mor₂) ≫ y = _
      rw [comp_distTriang_mor_zero₁₂ _ hT', F.map_zero, zero_comp, F.map_zero])
    obtain ⟨b, rfl⟩ := Triangle.yoneda_exact₂ _ hT' a this
    change T.obj₂ ⟶ Y at b
    have : (F.mapTriangle.obj T).mor₁ ≫ (y - F.map b) = 0 := by
      change F.map T.mor₁ ≫ (y - F.map b) = 0
      rw [comp_sub, ← ha, F.map_comp]
      exact sub_self _
    obtain ⟨c, hc⟩ := Triangle.yoneda_exact₂ _ hFT _ this
    obtain ⟨c', rfl⟩ := h₃.2 c
    refine ⟨b + T.mor₂ ≫ c', ?_⟩
    rw [F.map_add, F.map_comp]
    rw [sub_eq_iff_eq_add'] at hc
    rw [hc]
    rfl

end Triangulated

variable (F) [F.CommShift ℤ] [F.IsTriangulated]

/-- For fixed `X`, the objects `Y` such that `F` is bijective on `X⟦a⟧ ⟶ Y⟦b⟧` for all `a`, `b`
form a triangulated subcategory. -/
def homBijectiveShiftsRight (X : C) : ObjectProperty C := fun Y ↦ F.HomBijectiveShifts X Y

/-- For fixed `Y`, the objects `X` such that `F` is bijective on `X⟦a⟧ ⟶ Y⟦b⟧` for all `a`, `b`
form a triangulated subcategory. -/
def homBijectiveShiftsLeft (Y : C) : ObjectProperty C := fun X ↦ F.HomBijectiveShifts X Y

instance (X : C) : (F.homBijectiveShiftsRight X).IsClosedUnderIsomorphisms where
  of_iso e h a b := (h a b).of_iso (Iso.refl _) ((shiftFunctor C b).mapIso e)

instance (Y : C) : (F.homBijectiveShiftsLeft Y).IsClosedUnderIsomorphisms where
  of_iso e h a b := (h a b).of_iso ((shiftFunctor C a).mapIso e) (Iso.refl _)

instance isTriangulated_homBijectiveShiftsRight (X : C) :
    (F.homBijectiveShiftsRight X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun _ _ ↦
    HomBijective.of_isZero_right ((shiftFunctor C _).map_isZero (isZero_zero C))⟩
  isStableUnderShiftBy c := ⟨fun _ h ↦ HomBijectiveShifts.shift_right h c⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ a b ↦ by
    have hT' := Triangle.shift_distinguished T hT b
    refine homBijective_obj₂_of_triangle _ _ hT' (h₁ a b) (h₃ a b) ?_ ?_
    · exact ((h₃ a (b - 1)).of_iso (Iso.refl _)
        ((shiftFunctorAdd' C b (-1) (b - 1) (by lia)).app _)).2
    · exact ((h₁ a (b + 1)).of_iso (Iso.refl _)
        ((shiftFunctorAdd' C b 1 (b + 1) rfl).app _)).1

instance isTriangulated_homBijectiveShiftsLeft (Y : C) :
    (F.homBijectiveShiftsLeft Y).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun _ _ ↦
    HomBijective.of_isZero_left ((shiftFunctor C _).map_isZero (isZero_zero C))⟩
  isStableUnderShiftBy c := ⟨fun _ h ↦ HomBijectiveShifts.shift_left h c⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ a b ↦ by
    have hT' := Triangle.shift_distinguished T hT a
    refine homBijective_obj₂_of_triangle' _ _ hT' (h₁ a b) (h₃ a b) ?_ ?_
    · exact ((h₃ (a - 1) b).of_iso
        ((shiftFunctorAdd' C a (-1) (a - 1) (by lia)).app _) (Iso.refl _)).1
    · exact ((h₁ (a + 1) b).of_iso
        ((shiftFunctorAdd' C a 1 (a + 1) rfl).app _) (Iso.refl _)).2

/-- If every object of `C` lies in every triangulated subcategory, closed under isomorphisms,
containing `G`, and `F` is bijective on the morphisms `G⟦a⟧ ⟶ G⟦b⟧`, then `F` is bijective on
all morphisms. -/
lemma homBijective_of_generator {G : C}
    (hG : ∀ (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms], P G →
      ∀ X, P X)
    (hGG : F.HomBijectiveShifts G G) (X Y : C) : F.HomBijective X Y := by
  have h₁ : ∀ Y, F.HomBijectiveShifts G Y := hG (F.homBijectiveShiftsRight G) hGG
  exact (hG (F.homBijectiveShiftsLeft Y) (h₁ Y) X).homBijective

/-- If every object of `C` lies in every triangulated subcategory, closed under isomorphisms,
containing `G`, and `F` is bijective on the morphisms `G⟦a⟧ ⟶ G⟦b⟧`, then `F` is fully
faithful. -/
noncomputable def fullyFaithfulOfGenerator {G : C}
    (hG : ∀ (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms], P G →
      ∀ X, P X)
    (hGG : F.HomBijectiveShifts G G) : F.FullyFaithful where
  preimage {X Y} := (Equiv.ofBijective _ (F.homBijective_of_generator hG hGG X Y)).symm
  map_preimage {X Y} f :=
    (Equiv.ofBijective _ (F.homBijective_of_generator hG hGG X Y)).apply_symm_apply f
  preimage_map {X Y} f :=
    (Equiv.ofBijective _ (F.homBijective_of_generator hG hGG X Y)).symm_apply_apply f

end Functor

end CategoryTheory

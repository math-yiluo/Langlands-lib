/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru

/-!
# Image subobjects

We record some facts about the image subobject `imageSubobject f` of a morphism `f`.

* `imageSubobject f` is the smallest subobject through which `f` factors, it is computed by
  any epi-mono factorisation of `f`, and the image pushforward `Subobject.«exists» f` is an
  image subobject.
* Precomposing `f` with an epimorphism does not change `imageSubobject f`, and a morphism
  into a subobject `T` of `X` is an epimorphism as soon as the image of its composition with
  `T.arrow` is `T`.

## Main results

- `CategoryTheory.Limits.imageSubobject_comp_of_epi`
- `CategoryTheory.Limits.epi_of_imageSubobject_comp_arrow_eq`
- `CategoryTheory.Subobject.imageSubobject_le_iff`
- `CategoryTheory.Subobject.imageSubobject_eq_mk`
- `CategoryTheory.Subobject.exists_obj_eq_imageSubobject`
- `CategoryTheory.Subobject.exists_obj_top`
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

open Subobject

variable {C : Type u} [Category.{v} C]

section

variable [Balanced C] [HasImages C] [HasEqualizers C] {A B X : C}

/-- Precomposing with an epimorphism does not change the image subobject. -/
lemma imageSubobject_comp_of_epi (e : A ⟶ B) [Epi e] (m : B ⟶ X) :
    imageSubobject (e ≫ m) = imageSubobject m := by
  have : IsIso (image.preComp e m) := isIso_of_mono_of_epi _
  exact mk_eq_mk_of_comm _ _ (asIso (image.preComp e m)) (image.preComp_ι e m)

/-- If the image of `q ≫ T.arrow` is the whole of the subobject `T`, then `q` is an
epimorphism. -/
lemma epi_of_imageSubobject_comp_arrow_eq {T : Subobject X} (q : A ⟶ (T : C))
    (hq : imageSubobject (q ≫ T.arrow) = T) : Epi q := by
  have hfac : factorThruImageSubobject q ≫ (imageSubobject q).arrow = q :=
    imageSubobject_arrow_comp q
  have h₀ : imageSubobject (q ≫ T.arrow) =
      Subobject.mk ((imageSubobject q).arrow ≫ T.arrow) := by
    conv_lhs => rw [← hfac]
    rw [Category.assoc, imageSubobject_comp_of_epi, imageSubobject_mono]
  have h₁ : Subobject.mk ((imageSubobject q).arrow ≫ T.arrow) = Subobject.mk T.arrow := by
    rw [← h₀, hq, Subobject.mk_arrow]
  have h₂ : (Subobject.isoOfMkEqMk ((imageSubobject q).arrow ≫ T.arrow) T.arrow h₁).hom =
      (imageSubobject q).arrow := by
    rw [← cancel_mono T.arrow]
    simp
  have : IsIso (imageSubobject q).arrow :=
    h₂ ▸ (inferInstance :
      IsIso (Subobject.isoOfMkEqMk ((imageSubobject q).arrow ≫ T.arrow) T.arrow h₁).hom)
  rw [← hfac]
  infer_instance

end

end CategoryTheory.Limits

namespace CategoryTheory.Subobject

open Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- `imageSubobject f` is the smallest subobject through which `f` factors. -/
theorem imageSubobject_le_iff (f : X ⟶ Y) [HasImage f] (T : Subobject Y) :
    imageSubobject f ≤ T ↔ T.Factors f := by
  rw [imageSubobject, mk_le_iff_factors]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← image.fac f]
    exact factors_of_factors_right _ h
  · rw [← image.lift_fac (F' := { I := (T : C), m := T.arrow, e := T.factorThru f h })]
    exact factors_comp_arrow _

/-- An epi-mono factorisation computes the image subobject. -/
theorem imageSubobject_eq_mk [HasStrongEpiMonoFactorisations C] {I : C} (e : X ⟶ I) (i : I ⟶ Y)
    [StrongEpi e] [Mono i] : imageSubobject (e ≫ i) = mk i :=
  (mk_eq_mk_of_comm i (image.ι (e ≫ i)) (image.isoStrongEpiMono e i rfl) (by simp)).symm

variable [HasImages C]

/-- The image pushforward of a subobject is the image subobject of the composition. -/
theorem exists_obj_eq_imageSubobject (f : X ⟶ Y) (S : Subobject X) :
    («exists» f).obj S = imageSubobject (S.arrow ≫ f) :=
  le_antisymm ((exists_le_iff f S _).2 ((imageSubobject_le_iff _ _).1 le_rfl))
    ((imageSubobject_le_iff _ _).2 ((exists_le_iff f S _).1 le_rfl))

/-- The image pushforward of the top subobject is the image subobject. -/
theorem exists_obj_top [HasEqualizers C] (f : X ⟶ Y) :
    («exists» f).obj ⊤ = imageSubobject f := by
  rw [exists_obj_eq_imageSubobject, imageSubobject_iso_comp]

end CategoryTheory.Subobject

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Recognising (co)fans as (co)limits

A cofan (resp. fan) is a colimit (resp. limit) if and only if the induced maps on morphisms are
bijective, and limit fans are stable under isomorphisms of families. If all factors of a product
but one are zero objects, then a morphism into the product is an isomorphism as soon as its
component in the remaining factor is.

## Main statements

- `CategoryTheory.Limits.Cofan.IsColimit.ofBijective`,
  `CategoryTheory.Limits.Fan.IsLimit.ofBijective`.
- `CategoryTheory.Limits.Fan.IsLimit.ofIsos`.
- `CategoryTheory.Limits.isIso_pi_lift_of_isZero`.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {β : Type*} {X : β → C}

/-- A cofan `s` is a colimit if for any object `Y`, the precomposition with the coprojections
induces a bijection `(s.pt ⟶ Y) → ∀ j, (X j ⟶ Y)`. -/
noncomputable def Cofan.IsColimit.ofBijective (s : Cofan X)
    (h : ∀ Y, Function.Bijective fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g) : IsColimit s :=
  Cofan.IsColimit.mk s (fun t ↦ (Equiv.ofBijective _ (h t.pt)).symm t.inj)
    (fun t j ↦ congrFun ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.inj) j)
    (fun t _ hm ↦ (h t.pt).1
      ((funext hm).trans ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.inj).symm))

/-- A fan `s` is a limit if for any object `Y`, the composition with the projections
induces a bijection `(Y ⟶ s.pt) → ∀ j, (Y ⟶ X j)`. -/
noncomputable def Fan.IsLimit.ofBijective (s : Fan X)
    (h : ∀ Y, Function.Bijective fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) : IsLimit s :=
  Fan.IsLimit.mk s (fun t ↦ (Equiv.ofBijective _ (h t.pt)).symm t.proj)
    (fun t j ↦ congrFun ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.proj) j)
    (fun t _ hm ↦ (h t.pt).1
      ((funext hm).trans ((Equiv.ofBijective _ (h t.pt)).apply_symm_apply t.proj).symm))

lemma Cofan.IsColimit.bijective {s : Cofan X} (hs : IsColimit s) (Y : C) :
    Function.Bijective fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g :=
  ⟨fun _ _ h ↦ Cofan.IsColimit.hom_ext hs _ _ (congrFun h),
    fun f ↦ ⟨Cofan.IsColimit.desc hs f, funext (Cofan.IsColimit.fac hs f)⟩⟩

lemma Fan.IsLimit.bijective {s : Fan X} (hs : IsLimit s) (Y : C) :
    Function.Bijective fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j :=
  ⟨fun _ _ h ↦ Fan.IsLimit.hom_ext hs _ _ (congrFun h),
    fun f ↦ ⟨Fan.IsLimit.lift hs f, funext (Fan.IsLimit.fac hs f)⟩⟩

/-- The bijectivity condition of `Cofan.IsColimit.ofBijective` is invariant under isomorphisms
of the target. -/
lemma Cofan.bijective_of_iso (s : Cofan X) {Y Y' : C} (e : Y ≅ Y')
    (h : Function.Bijective fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g) :
    Function.Bijective fun (g : s.pt ⟶ Y') (j : β) ↦ s.inj j ≫ g := by
  have : (fun (g : s.pt ⟶ Y') (j : β) ↦ s.inj j ≫ g) =
      (Equiv.piCongrRight fun j ↦ (Iso.refl (X j)).homCongr e) ∘
        (fun (g : s.pt ⟶ Y) (j : β) ↦ s.inj j ≫ g) ∘ ((Iso.refl s.pt).homCongr e).symm := by
    ext g j
    simp
  rw [this]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

/-- The bijectivity condition of `Fan.IsLimit.ofBijective` is invariant under isomorphisms
of the source. -/
lemma Fan.bijective_of_iso (s : Fan X) {Y Y' : C} (e : Y ≅ Y')
    (h : Function.Bijective fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) :
    Function.Bijective fun (g : Y' ⟶ s.pt) (j : β) ↦ g ≫ s.proj j := by
  have : (fun (g : Y' ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) =
      (Equiv.piCongrRight fun j ↦ e.homCongr (Iso.refl (X j))) ∘
        (fun (g : Y ⟶ s.pt) (j : β) ↦ g ≫ s.proj j) ∘ (e.homCongr (Iso.refl s.pt)).symm := by
    ext g j
    simp
  rw [this]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {β : Type*} {X Y : β → C}

/-- A fan over `X` is a limit if it is isomorphic to a limit fan over a family `Y` isomorphic
to `X`. -/
noncomputable def Fan.IsLimit.ofIsos {s : Fan X} {t : Fan Y} (ht : IsLimit t)
    (e : ∀ j, X j ≅ Y j) (a : s.pt ≅ t.pt) (w : ∀ j, a.hom ≫ t.proj j = s.proj j ≫ (e j).hom) :
    IsLimit s :=
  have w' (j : β) : a.inv ≫ s.proj j = t.proj j ≫ (e j).inv := by
    rw [← cancel_epi a.hom, Iso.hom_inv_id_assoc, reassoc_of% (w j), Iso.hom_inv_id, comp_id]
  Fan.IsLimit.mk _ (fun u ↦ Fan.IsLimit.lift ht (fun j ↦ u.proj j ≫ (e j).hom) ≫ a.inv)
    (fun u j ↦ by simp [w'])
    (fun u m hm ↦ by
      rw [← cancel_mono a.hom, assoc, Iso.inv_hom_id, comp_id]
      exact Fan.IsLimit.hom_ext ht _ _ fun j ↦ by simp [w, reassoc_of% (hm j)])

/-- A morphism between the points of limit fans over isomorphic families which is compatible
with the projections is an isomorphism. -/
lemma Fan.IsLimit.isIso_of_isos {s : Fan X} {t : Fan Y} (hs : IsLimit s) (ht : IsLimit t)
    (e : ∀ j, X j ≅ Y j) (f : s.pt ⟶ t.pt) (w : ∀ j, f ≫ t.proj j = s.proj j ≫ (e j).hom) :
    IsIso f :=
  ⟨Fan.IsLimit.lift hs fun j ↦ t.proj j ≫ (e j).inv,
    Fan.IsLimit.hom_ext hs _ _ fun j ↦ by simp [reassoc_of% (w j)],
    Fan.IsLimit.hom_ext ht _ _ fun j ↦ by simp [w]⟩

end CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- A morphism `Pi.lift g` into a product `∏ᶜ f` is an isomorphism if its component `g t` is an
isomorphism and all other factors `f b`, `b ≠ t`, are zero objects. -/
lemma isIso_pi_lift_of_isZero {β : Type*} {C : Type*} [Category* C] {f : β → C}
    [HasProduct f] {A : C} (g : ∀ b, A ⟶ f b) (t : β) (ht : IsIso (g t))
    (hz : ∀ b, b ≠ t → IsZero (f b)) : IsIso (Pi.lift g) := by
  classical
  refine ⟨⟨Pi.π f t ≫ inv (g t), by simp, Pi.hom_ext _ _ fun b ↦ ?_⟩⟩
  by_cases h : b = t
  · subst h
    simp
  · exact (hz b h).eq_of_tgt _ _

end CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- **Universal property of a product.** For a family `f : β → C` having a product `∏ᶜ f`, with
projections `Pi.π f b`, every family of morphisms `g b : L ⟶ f b` factors through exactly one
morphism `L ⟶ ∏ᶜ f`, namely `Pi.lift g`. Products of morphisms are `Pi.map`, and a category has
countable products (`CategoryTheory.Limits.HasCountableProducts`) if every family indexed by a
countable type has a product. (blueprint: `def-weil-category-product`) -/
theorem Pi.existsUnique_lift {β : Type*} {C : Type*} [Category* C] (f : β → C) [HasProduct f]
    {L : C} (g : ∀ b, L ⟶ f b) : ∃! h : L ⟶ ∏ᶜ f, ∀ b, h ≫ Pi.π f b = g b :=
  ⟨Pi.lift g, fun b ↦ Pi.lift_comp_π g b, fun h hh ↦ Pi.hom_ext _ _ fun b ↦ by simp [hh]⟩


end CategoryTheory.Limits

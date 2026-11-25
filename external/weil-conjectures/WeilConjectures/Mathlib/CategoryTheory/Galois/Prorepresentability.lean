/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# Any two fibre functors on a Galois category are isomorphic

Let `F` be a fibre functor on a Galois category `C`. By pro-representability of `F`
(`CategoryTheory.PreGaloisCategory.PointedGaloisObject.isColimit`), natural transformations
from `F` to any functor `F'` to finite sets are the compatible families of elements of `F'` on
the pointed Galois objects of `F` (`CategoryTheory.PreGaloisCategory.homEquivSectionsFibers`).
If `F'` is a fibre functor too, such a family exists, since the fibres of `F'` on Galois objects
form a cofiltered system of nonempty finite sets, and every natural transformation between
fibre functors is an isomorphism. Hence any two fibre functors are isomorphic
(`CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor`): in the case of finite étale
covers of a connected scheme, any two geometric points are joined by a path.

## Main statements

- `CategoryTheory.PreGaloisCategory.homEquivSectionsFibers`
- `CategoryTheory.PreGaloisCategory.isIso_of_fiberFunctor`
- `CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor`
-/

@[expose] public section

universe u₁ u₂

namespace CategoryTheory.PreGaloisCategory

open Limits CategoryTheory.Functor PointedGaloisObject

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
  (F F' : C ⥤ FintypeCat.{u₂}) [FiberFunctor F]

/-- The natural transformations from a fibre functor `F` to a functor `F'` to finite sets are
the compatible families of elements of `F'` on the pointed Galois objects of `F`, by
pro-representability of `F`. -/
noncomputable def homEquivSectionsFibers :
    (F ⟶ F') ≃ (incl F ⋙ F' ⋙ FintypeCat.incl).sections :=
  let i1 : (F ⟶ F') ≃ (F ⋙ FintypeCat.incl ⟶ F' ⋙ FintypeCat.incl) :=
    (FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let i2 : (F ⋙ FintypeCat.incl ⟶ F' ⋙ FintypeCat.incl) ≅
      (colimit ((incl F).op ⋙ coyoneda) ⟶ F' ⋙ FintypeCat.incl) :=
    (yoneda.obj (F' ⋙ FintypeCat.incl)).mapIso
      (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ F' ⋙ FintypeCat.incl) ≅
      limit ((incl F ⋙ F' ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁}) :=
    colimitCoyonedaHomIsoLimit' (incl F) (F' ⋙ FintypeCat.incl)
  let i4 : limit (incl F ⋙ (F' ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁}) ≃
      ((incl F ⋙ F' ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁}).sections :=
    Types.limitEquivSections (incl F ⋙ (F' ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁, u₂})
  let i5 : ((incl F ⋙ F' ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u₁}).sections ≃
      (incl F ⋙ F' ⋙ FintypeCat.incl).sections :=
    (Types.sectionsEquiv (incl F ⋙ F' ⋙ FintypeCat.incl)).symm
  i1.trans <| i2.toEquiv.trans <| i3.toEquiv.trans <| i4.trans i5

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma homEquivSectionsFibers_π (f : F ⟶ F') (A : PointedGaloisObject F) :
    (homEquivSectionsFibers F F' f).val A = f.app A A.pt := by
  dsimp [homEquivSectionsFibers, Types.sectionsEquiv]
  erw [Types.limitEquivSections_apply, colimitCoyonedaHomIsoLimit'_π_apply]
  change (((FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful
      FintypeCat.incl) C).homEquiv) f).app A
    (((colimit.ι _ _) ≫ (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).hom).app
      A _) = f.app A A.pt
  simp
  rfl

lemma homEquivSectionsFibers_symm_app (s : (incl F ⋙ F' ⋙ FintypeCat.incl).sections)
    (A : PointedGaloisObject F) :
    ((homEquivSectionsFibers F F').symm s).app A A.pt = s.val A := by
  rw [← homEquivSectionsFibers_π, Equiv.apply_symm_apply]

variable [FiberFunctor F']

/-- A natural transformation `η : F ⟶ F'` between fibre functors is bijective on the fibre of a
Galois object `A`: it is `Aut A`-equivariant, `Aut A` acts transitively on `F.obj A` and freely
on `F'.obj A`, and the two fibres have the same cardinality as `Aut A`. -/
lemma bijective_app_of_isGalois (η : F ⟶ F') (A : C) [IsGalois A] :
    Function.Bijective (η.app A) := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  have hinj : Function.Injective (η.app A) := by
    intro x y hxy
    obtain ⟨σ, rfl⟩ := (evaluation_aut_bijective_of_isGalois F A a).2 x
    obtain ⟨τ, rfl⟩ := (evaluation_aut_bijective_of_isGalois F A a).2 y
    have h₁ := ConcreteCategory.congr_hom (η.naturality σ.asIso.hom) a
    have h₂ := ConcreteCategory.congr_hom (η.naturality τ.asIso.hom) a
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    have : σ = τ := evaluation_aut_injective_of_isConnected F' A (η.app A a) (by
      simp only at hxy ⊢
      rw [← h₁, ← h₂, hxy])
    rw [this]
  refine ⟨hinj, ?_⟩
  have hcard : Nat.card (F.obj A) = Nat.card (F'.obj A) := by
    obtain ⟨b⟩ := nonempty_fiber_of_isConnected F' A
    rw [← Nat.card_congr (evaluationEquivOfIsGalois F A a),
      ← Nat.card_congr (evaluationEquivOfIsGalois F' A b)]
  exact (Function.Injective.bijective_of_nat_card_le hinj hcard.ge).2

/-- Every natural transformation between fibre functors is bijective on all fibres. -/
lemma bijective_app_of_fiberFunctor (η : F ⟶ F') (X : C) :
    Function.Bijective (η.app X) := by
  have hnat {Y Z : C} (u : Y ⟶ Z) (y : F.obj Y) : η.app Z (F.map u y) = F'.map u (η.app Y y) :=
    by simp only [← ConcreteCategory.comp_apply, η.naturality]
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨Z, f, z, _, hfz⟩ := exists_hom_from_galois_of_fiber F (X ⨯ X)
      ((fiberBinaryProductEquiv F X X).symm (x, y))
    have hx : F.map (f ≫ prod.fst) z = x := by
      simp [F.map_comp, hfz, fiberBinaryProductEquiv_symm_fst_apply]
    have hy : F.map (f ≫ prod.snd) z = y := by
      simp [F.map_comp, hfz, fiberBinaryProductEquiv_symm_snd_apply]
    have : f ≫ prod.fst = f ≫ prod.snd := by
      apply evaluation_injective_of_isConnected F' Z X (η.app Z z)
      simp only
      rw [← hnat, ← hnat, hx, hy, hxy]
    rw [← hx, ← hy, this]
  · obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F' X y
    obtain ⟨a', rfl⟩ := (bijective_app_of_isGalois F F' η A).2 a
    exact ⟨F.map f a', hnat f a'⟩

/-- Every natural transformation between fibre functors is an isomorphism. -/
lemma isIso_of_fiberFunctor (η : F ⟶ F') : IsIso η := by
  have (X : C) : IsIso (η.app X) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_app_of_fiberFunctor F F' η X)
  exact NatIso.isIso_of_isIso_app η

/-- **Any two fibre functors on a Galois category are isomorphic.** The fibres of `F'` on the
pointed Galois objects of `F` form a cofiltered system of nonempty finite sets, so it has a
section, which is a natural transformation `F ⟶ F'` by pro-representability of `F`; it is an
isomorphism since `F` and `F'` are fibre functors. -/
theorem nonempty_iso_of_fiberFunctor : Nonempty (F ≅ F') := by
  have (A : PointedGaloisObject F) : Nonempty ((incl F ⋙ F' ⋙ FintypeCat.incl).obj A) :=
    nonempty_fiber_of_isConnected F' A.obj
  have (A : PointedGaloisObject F) : Finite ((incl F ⋙ F' ⋙ FintypeCat.incl).obj A) :=
    inferInstanceAs (Finite (F'.obj A.obj))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system
    (incl F ⋙ F' ⋙ FintypeCat.incl)
  have := isIso_of_fiberFunctor F F' ((homEquivSectionsFibers F F').symm ⟨s, hs⟩)
  exact ⟨asIso ((homEquivSectionsFibers F F').symm ⟨s, hs⟩)⟩

end CategoryTheory.PreGaloisCategory

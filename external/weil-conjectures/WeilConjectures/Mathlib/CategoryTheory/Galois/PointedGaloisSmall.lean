/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Pointed Galois objects form an essentially small category

Let `C` be a Galois category with a fibre functor `F`. If `C` is essentially small, then so is
the category `PointedGaloisObject F` of pointed Galois objects: an isomorphism class of pointed
Galois objects `(A, a)` is determined by the isomorphism class of `A` together with a point of the
fibre of a fixed representative of it. Being Galois and being connected are invariant under
isomorphism.

This is used to index the universal profinite étale cover, a limit over the pointed Galois
objects, by a small category.

## Main results

- `CategoryTheory.PreGaloisCategory.isConnected_of_iso`, `isGalois_of_iso`: connectedness and the
  Galois property are invariant under isomorphism.
- `CategoryTheory.PreGaloisCategory.essentiallySmall_pointedGaloisObject`: pointed Galois objects
  form an essentially small category.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C]

/-- Connectedness is invariant under isomorphism. -/
lemma isConnected_of_iso {X Y : C} (e : X ≅ Y) [IsConnected X] : IsConnected Y where
  notInitial h := IsConnected.notInitial (X := X) (h.ofIso e.symm)
  noTrivialComponent Z i _ hZ := by
    have : IsIso (i ≫ e.inv) := IsConnected.noTrivialComponent Z (i ≫ e.inv) hZ
    have h : i = (i ≫ e.inv) ≫ e.hom := by simp
    rw [h]
    infer_instance

variable [GaloisCategory C]

/-- Being Galois is invariant under isomorphism. -/
lemma isGalois_of_iso {X Y : C} (e : X ≅ Y) [IsGalois X] : IsGalois Y := by
  obtain ⟨F, hF⟩ := GaloisCategory.hasFiberFunctor (C := C)
  have : IsConnected Y := isConnected_of_iso e
  rw [isGalois_iff_pretransitive F]
  refine ⟨fun y₁ y₂ ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut X) (F.map e.inv y₁) (F.map e.inv y₂)
  refine ⟨.of (e.symm ≪≫ σ.asIso ≪≫ e), ?_⟩
  change F.map (e.inv ≫ σ.asIso.hom ≫ e.hom) y₁ = y₂
  change F.map σ.asIso.hom (F.map e.inv y₁) = F.map e.inv y₂ at hσ
  rw [F.map_comp, F.map_comp, FintypeCat.comp_apply, FintypeCat.comp_apply, hσ,
    ← FintypeCat.comp_apply, ← F.map_comp, e.inv_hom_id, F.map_id, FintypeCat.id_apply]

/-- **Pointed Galois objects form an essentially small category** if `C` is essentially
small: the isomorphism class of `(A, a)` is the image of the isomorphism class `[A]` of `A`
together with a point of the fibre of the chosen representative of `[A]`. -/
theorem essentiallySmall_pointedGaloisObject [EssentiallySmall.{w} C]
    (F : C ⥤ FintypeCat.{w}) : EssentiallySmall.{w} (PointedGaloisObject F) := by
  have : LocallySmall.{w} C := inferInstance
  have : Small.{w} (Skeleton C) := ((essentiallySmall_iff C).1 ‹_›).1
  have hψ (A : C) : Nonempty ((toSkeleton A).out ≅ A) :=
    Quotient.mk_out (s := isIsomorphicSetoid C) A
  let g : (Σ X : {X : Skeleton C // IsGalois X.out}, F.obj X.1.out) →
      Skeleton (PointedGaloisObject F) :=
    fun x ↦ toSkeleton ⟨x.1.1.out, x.2, x.1.2⟩
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨A, rfl⟩ : ∃ A, toSkeleton A = x := ⟨x.out, Quotient.out_eq x⟩
    obtain ⟨ψ⟩ := hψ A.obj
    have : IsGalois (toSkeleton A.obj).out := isGalois_of_iso ψ.symm
    refine ⟨⟨⟨toSkeleton A.obj, this⟩, F.map ψ.inv A.pt⟩, Quotient.sound ⟨?_⟩⟩
    exact
      { hom := ⟨ψ.hom, by
          change F.map ψ.hom (F.map ψ.inv A.pt) = A.pt
          rw [← FintypeCat.comp_apply, ← F.map_comp, ψ.inv_hom_id, F.map_id,
            FintypeCat.id_apply]⟩
        inv := ⟨ψ.inv, rfl⟩
        hom_inv_id := PointedGaloisObject.hom_ext ψ.hom_inv_id
        inv_hom_id := PointedGaloisObject.hom_ext ψ.inv_hom_id }
  have : Small.{w} (Skeleton (PointedGaloisObject F)) := small_of_surjective hg
  have : LocallySmall.{w} (PointedGaloisObject F) :=
    ⟨fun A B ↦ small_of_injective (f := fun φ : A ⟶ B ↦ φ.val)
      fun _ _ h ↦ PointedGaloisObject.hom_ext h⟩
  exact (essentiallySmall_iff _).2 ⟨inferInstance, inferInstance⟩

end CategoryTheory.PreGaloisCategory

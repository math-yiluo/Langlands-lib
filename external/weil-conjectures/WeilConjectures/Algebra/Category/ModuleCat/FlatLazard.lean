/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Lazard's theorem: a flat module is a filtered colimit of finite free modules

For a module `M` over a commutative ring `R`, consider the category `ModuleCat.FinFreeOver M` of
linear maps `R^n ⟶ M` from finite free modules (written `Fin n →₀ R`), with morphisms the
linear maps `R^n ⟶ R^m` over `M`. If `M` is flat, this category is filtered
(`ModuleCat.FinFreeOver.isFiltered`) and `M` is the colimit of the forgetful diagram
(`ModuleCat.FinFreeOver.isColimitCocone`): this is Lazard's theorem (Stacks, Tag 058G). Both
statements are consequences of the equational criterion for flatness
(`Module.Flat.exists_factorization_of_comp_eq_zero_of_free`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- A linear map `R^n ⟶ M` from a finite free module to `M`. -/
structure FinFreeOver where
  /-- The rank of the finite free module. -/
  n : ℕ
  /-- The linear map to `M`. -/
  f : (Fin n →₀ R) →ₗ[R] M

namespace FinFreeOver

variable {M}

/-- The morphisms of `ModuleCat.FinFreeOver M` are the linear maps between the finite free
modules compatible with the maps to `M`. -/
instance : Category (FinFreeOver M) where
  Hom A B := { g : (Fin A.n →₀ R) →ₗ[R] (Fin B.n →₀ R) // B.f ∘ₗ g = A.f }
  id A := ⟨LinearMap.id, by simp⟩
  comp g h := ⟨h.1 ∘ₗ g.1, by rw [← LinearMap.comp_assoc, h.2, g.2]⟩

@[ext]
lemma hom_ext {A B : FinFreeOver M} {g h : A ⟶ B} (e : g.1 = h.1) : g = h :=
  Subtype.ext e

@[simp]
lemma id_val (A : FinFreeOver M) : (𝟙 A : A ⟶ A).1 = LinearMap.id := rfl

@[simp]
lemma comp_val {A B C : FinFreeOver M} (g : A ⟶ B) (h : B ⟶ C) : (g ≫ h).1 = h.1 ∘ₗ g.1 := rfl

lemma w {A B : FinFreeOver M} (g : A ⟶ B) : B.f ∘ₗ g.1 = A.f := g.2

variable (M)

/-- The forgetful diagram `(R^n ⟶ M) ↦ R^n`. -/
@[simps]
noncomputable def diagram : FinFreeOver M ⥤ ModuleCat.{u} R where
  obj A := ModuleCat.of R (Fin A.n →₀ R)
  map g := ModuleCat.ofHom g.1

/-- The tautological cocone over the forgetful diagram, with point `M`. -/
@[simps]
noncomputable def cocone : Cocone (diagram M) where
  pt := M
  ι :=
    { app A := ModuleCat.ofHom A.f
      naturality A B g := by
        ext x
        exact LinearMap.congr_fun g.2 x }

variable [Module.Flat R M]

/-- **Lazard's theorem**, filteredness: for a flat module `M`, the category of linear maps
`R^n ⟶ M` from finite free modules is filtered. -/
instance isFiltered : IsFiltered (FinFreeOver M) where
  nonempty := ⟨⟨0, 0⟩⟩
  cocone_objs A B := by
    obtain ⟨k, a, y, hya, -⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free
      (K := PUnit.{u + 1}) (f := (0 : PUnit.{u + 1} →ₗ[R] (Fin A.n →₀ R) × (Fin B.n →₀ R)))
      (x := A.f.coprod B.f) (by simp)
    refine ⟨⟨k, y⟩, ⟨a ∘ₗ LinearMap.inl R _ _, ?_⟩, ⟨a ∘ₗ LinearMap.inr R _ _, ?_⟩, trivial⟩
    · rw [← LinearMap.comp_assoc, ← hya]
      ext
      simp
    · rw [← LinearMap.comp_assoc, ← hya]
      ext
      simp
  cocone_maps {A B} g h := by
    obtain ⟨k, a, y, hya, ha⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free
      (f := g.1 - h.1) (x := B.f) (by rw [LinearMap.comp_sub, g.2, h.2, sub_self])
    refine ⟨⟨k, y⟩, ⟨a, hya.symm⟩, ?_⟩
    ext1
    rw [LinearMap.comp_sub] at ha
    exact sub_eq_zero.1 ha

/-- **Lazard's theorem**: a flat module `M` is the filtered colimit of the finite free modules
`R^n` mapping to it. -/
noncomputable def isColimitCocone : IsColimit (cocone M) := by
  have : ReflectsColimitsOfShape (FinFreeOver M) (forget (ModuleCat.{u} R)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget (ModuleCat.{u} R)) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun A x y hxy ↦ ?_)
  · let x' : M := x
    refine ⟨⟨1, Finsupp.linearCombination R (fun _ ↦ x')⟩, Finsupp.single 0 1, ?_⟩
    exact (by simp : Finsupp.linearCombination R (fun _ : Fin 1 ↦ x')
      (Finsupp.single 0 1) = x').symm
  · let x' : Fin A.n →₀ R := x
    let y'' : Fin A.n →₀ R := y
    have hxy' : A.f (x' - y'') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    obtain ⟨k, a, y', hya, ha⟩ := Module.Flat.exists_factorization_of_apply_eq_zero_of_free hxy'
    refine ⟨⟨k, y'⟩, ⟨a, hya.symm⟩, ?_⟩
    rw [map_sub, sub_eq_zero] at ha
    exact ha

end FinFreeOver

end ModuleCat

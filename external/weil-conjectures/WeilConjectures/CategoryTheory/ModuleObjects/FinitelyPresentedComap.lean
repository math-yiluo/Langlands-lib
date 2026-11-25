/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Finitely presented module objects under restriction of scalars along an isomorphism

Let `φ : R ⟶ S` be an isomorphism of algebra objects in an abelian monoidal closed category.
Restriction of scalars `Mod.comap φ` is additive (`CategoryTheory.Mod.comap_additive`) and maps
the free module `S` to the free module `R` (`CategoryTheory.Mod.regularIsoComapRegular`), hence
finitely presented `S`-modules to finitely presented `R`-modules
(`CategoryTheory.Mod.IsFinitelyPresented.comap`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C] {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S)
  [IsMonHom φ]

/-- Restriction of scalars is additive. -/
instance comap_additive : (comap φ : Mod C S ⥤ Mod C R).Additive where
  map_add := rfl

end Preadditive

variable {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- Along an isomorphism of algebra objects `φ : R ⟶ S`, the restriction of scalars of the free
module `S` is the free module `R`, via `φ`. -/
noncomputable def regularIsoComapRegular [IsIso φ] : regular R ≅ (comap φ).obj (regular S) :=
  isoMk (asIso φ) (by
    change μ[R] ≫ φ = R ◁ φ ≫ φ ▷ S ≫ μ[S]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

variable [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

/-- Along an isomorphism of algebra objects `φ : R ⟶ S`, the restriction of scalars of the free
module `S^n` is the free module `R^n`. -/
noncomputable def finiteFreeIsoComap [IsIso φ] (n : ℕ) :
    (comap φ).obj (finiteFree S n) ≅ finiteFree R n :=
  (comap φ).mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ (regularIsoComapRegular φ).symm

/-- Restriction of scalars along an isomorphism of algebra objects preserves finitely presented
module objects. -/
lemma IsFinitelyPresented.comap [IsIso φ] {N : Mod C S} (h : IsFinitelyPresented S N) :
    IsFinitelyPresented R ((Mod.comap φ).obj N) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := h
  exact ⟨n, m, (finiteFreeIsoComap φ m).inv ≫ (Mod.comap φ).map f ≫ (finiteFreeIsoComap φ n).hom,
    ⟨(Mod.comap φ).mapIso e ≪≫ PreservesCokernel.iso _ f ≪≫
      cokernel.mapIso _ _ (finiteFreeIsoComap φ m) (finiteFreeIsoComap φ n) (by simp)⟩⟩

end CategoryTheory.Mod

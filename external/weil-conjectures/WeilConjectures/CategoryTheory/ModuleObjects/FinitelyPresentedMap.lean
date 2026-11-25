/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap

/-!
# Finitely presented module objects under right exact functors

Finitely presented module objects are stable under isomorphism
(`CategoryTheory.Mod.IsFinitelyPresented.of_iso`). A functor `F : Mod_R ⥤ Mod_S` between
categories of module objects which is additive, right exact and sends the free module `R` to the
free module `S` preserves finitely presented module objects
(`CategoryTheory.Mod.IsFinitelyPresented.map`). Restriction of scalars along an isomorphism of
algebra objects reflects them (`CategoryTheory.Mod.IsFinitelyPresented.of_comap`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

section Iso

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- Being finitely presented is invariant under isomorphism of module objects. -/
lemma IsFinitelyPresented.of_iso {M N : Mod C R} (e : M ≅ N) (h : IsFinitelyPresented R M) :
    IsFinitelyPresented R N := by
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h
  exact ⟨n, m, f, ⟨e.symm ≪≫ e'⟩⟩

end Iso

section Map

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [Abelian D] [MonoidalPreadditive D]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]
  {S : D} [MonObj S] [PreservesFiniteColimits (tensorLeft S)]

/-- An additive right exact functor `F : Mod_R ⥤ Mod_S` with `F R ≅ S` sends the free module
`Rⁿ` to the free module `Sⁿ`. -/
noncomputable def finiteFreeIsoMap (F : Mod C R ⥤ Mod D S) [F.Additive]
    (e : F.obj (regular R) ≅ regular S) (n : ℕ) : F.obj (finiteFree R n) ≅ finiteFree S n :=
  F.mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ e

/-- An additive right exact functor `F : Mod_R ⥤ Mod_S` with `F R ≅ S` preserves finitely
presented module objects. -/
lemma IsFinitelyPresented.map (F : Mod C R ⥤ Mod D S) [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (regular R) ≅ regular S) {M : Mod C R} (h : IsFinitelyPresented R M) :
    IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h
  exact ⟨n, m, (finiteFreeIsoMap F e m).inv ≫ F.map f ≫ (finiteFreeIsoMap F e n).hom,
    ⟨F.mapIso e' ≪≫ PreservesCokernel.iso _ f ≪≫
      cokernel.mapIso _ _ (finiteFreeIsoMap F e m) (finiteFreeIsoMap F e n) (by simp)⟩⟩

end Map

section Comap

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [MonoidalClosed C] {R S : C} [MonObj R] [MonObj S] [PreservesFiniteColimits (tensorLeft R)]
  [PreservesFiniteColimits (tensorLeft S)]

/-- Restriction of scalars along an isomorphism `φ` of algebra objects reflects finitely
presented module objects. -/
lemma IsFinitelyPresented.of_comap (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] {N : Mod C S}
    (h : IsFinitelyPresented R ((Mod.comap φ).obj N)) : IsFinitelyPresented S N :=
  (h.comap (inv φ)).of_iso (((comapComp (inv φ) φ).app N).symm ≪≫
    (comapCongr (IsIso.inv_hom_id φ)).app N ≪≫ (comapId S).app N)

end Comap

end CategoryTheory.Mod

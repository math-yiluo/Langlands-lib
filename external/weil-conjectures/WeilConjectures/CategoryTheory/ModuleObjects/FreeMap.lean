/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap

/-!
# Free module objects under functors

Free module objects of finite rank are stable under isomorphism
(`CategoryTheory.Mod.IsFree.of_iso`), under additive functors `F : Mod_R ⥤ Mod_S` with
`F R ≅ S` (`CategoryTheory.Mod.IsFree.map`) and under restriction of scalars along an
isomorphism of algebra objects (`CategoryTheory.Mod.IsFree.comap`,
`CategoryTheory.Mod.IsFree.of_comap`). An additive right exact functor sending `R` to a free
module object of finite rank preserves finitely presented module objects
(`CategoryTheory.Mod.IsFinitelyPresented.map_of_isFree`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

section Free

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
  {D : Type*} [Category* D] [MonoidalCategory D] [Abelian D] [MonoidalPreadditive D]
  {S : D} [MonObj S] [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)]

omit [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)] in
/-- Being free of finite rank is invariant under isomorphism of module objects. -/
lemma IsFree.of_iso {M N : Mod C R} (e : M ≅ N) (h : IsFree R M) : IsFree R N := by
  obtain ⟨n, ⟨e'⟩⟩ := h
  exact ⟨n, ⟨e.symm ≪≫ e'⟩⟩

omit [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
  [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)] in
/-- An additive functor `F : Mod_R ⥤ Mod_S` with `F R ≅ S` preserves free module objects of
finite rank. -/
lemma IsFree.map (F : Mod C R ⥤ Mod D S) [F.Additive] (e : F.obj (regular R) ≅ regular S)
    {M : Mod C R} (h : IsFree R M) : IsFree S (F.obj M) := by
  obtain ⟨n, ⟨e'⟩⟩ := h
  exact ⟨n, ⟨F.mapIso e' ≪≫ finiteFreeIsoMap F e n⟩⟩

omit [PreservesFiniteColimits (MonoidalCategory.tensorLeft S)] in
variable (S) in
/-- A direct sum of `m` copies of `Sᵏ` is `S^{m k}`. -/
noncomputable def finiteFreeFiniteFreeIso (m k : ℕ) :
    (⨁ fun _ : Fin m ↦ finiteFree S k) ≅ finiteFree S (m * k) :=
  biproductBiproductIso (fun _ : Fin m ↦ Fin k) (fun _ _ ↦ regular S) ≪≫
    biproduct.whiskerEquiv (f := fun _ : (Σ _ : Fin m, Fin k) ↦ regular S)
      (g := fun _ : Fin (m * k) ↦ regular S)
      ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv) (fun _ ↦ Iso.refl _)

/-- An additive right exact functor `F : Mod_R ⥤ Mod_S` sending `R` to a free module object of
finite rank preserves finitely presented module objects: it sends a presentation
`Rᵐ ⟶ Rⁿ ⟶ M ⟶ 0` to a presentation `S^{m k} ⟶ S^{n k} ⟶ F M ⟶ 0`. -/
lemma IsFinitelyPresented.map_of_isFree (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F] (hF : IsFree S (F.obj (regular R))) {M : Mod C R}
    (h : IsFinitelyPresented R M) : IsFinitelyPresented S (F.obj M) := by
  obtain ⟨k, ⟨e⟩⟩ := hF
  let en (m : ℕ) : F.obj (finiteFree R m) ≅ finiteFree S (m * k) :=
    F.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ e) ≪≫ finiteFreeFiniteFreeIso S m k
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h
  exact ⟨n * k, m * k, (en m).inv ≫ F.map f ≫ (en n).hom,
    ⟨F.mapIso e' ≪≫ PreservesCokernel.iso _ f ≪≫
      cokernel.mapIso _ _ (en m) (en n) (by simp)⟩⟩

end Free

section Comap

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]

/-- Restriction of scalars along an isomorphism of algebra objects preserves free module objects
of finite rank. -/
lemma IsFree.comap {N : Mod C S} (h : IsFree S N) : IsFree R ((Mod.comap φ).obj N) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  exact ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫ finiteFreeIsoComap φ n⟩⟩

/-- Restriction of scalars along an isomorphism of algebra objects reflects free module objects
of finite rank. -/
lemma IsFree.of_comap {N : Mod C S} (h : IsFree R ((Mod.comap φ).obj N)) : IsFree S N :=
  (h.comap (inv φ)).of_iso (((comapComp (inv φ) φ).app N).symm ≪≫
    (comapCongr (IsIso.inv_hom_id φ)).app N ≪≫ (comapId S).app N)

end Comap

end CategoryTheory.Mod

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap

/-!
# Restriction of scalars along a finite free morphism of algebra objects

Let `φ : R ⟶ S` be a morphism of algebra objects in an abelian monoidal category such that `S`,
regarded as an `R`-module through `φ`, is finite free of rank `d`. Restriction of scalars then
sends the free module `Sⁿ` to the free module `R^{n d}`
(`CategoryTheory.Mod.comapFiniteFreeIso`), and, being additive and right exact, finitely
presented `S`-modules to finitely presented `R`-modules
(`CategoryTheory.Mod.IsFinitelyPresented.comap_of_finiteFree`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R S : C} [MonObj R] [MonObj S] [PreservesFiniteColimits (tensorLeft R)]
  [PreservesFiniteColimits (tensorLeft S)] (φ : R ⟶ S) [IsMonHom φ]

/-- A biproduct of `n` copies of the free module `Rᵈ` is the free module `R^{n d}`. -/
noncomputable def finiteFreeBiproductIso (n d : ℕ) :
    (⨁ fun _ : Fin n ↦ finiteFree R d) ≅ finiteFree R (n * d) :=
  biproductBiproductIso (fun _ : Fin n ↦ Fin d) (fun _ _ ↦ regular R) ≪≫
    biproduct.whiskerEquiv (g := fun _ : Fin (n * d) ↦ regular R)
      ((Equiv.sigmaEquivProd (Fin n) (Fin d)).trans finProdFinEquiv) (fun _ ↦ Iso.refl _)

/-- If the restriction of scalars of the free module `S` is the free module `Rᵈ`, then the
restriction of scalars of `Sⁿ` is `R^{n d}`. -/
noncomputable def comapFiniteFreeIso {d : ℕ} (e : (comap φ).obj (regular S) ≅ finiteFree R d)
    (n : ℕ) : (comap φ).obj (finiteFree S n) ≅ finiteFree R (n * d) :=
  (comap φ).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ e) ≪≫ finiteFreeBiproductIso n d

/-- If `S` is finite free as an `R`-module, restriction of scalars along `φ : R ⟶ S` preserves
finitely presented module objects: it is additive and right exact, and sends free modules of
finite rank to free modules of finite rank. -/
lemma IsFinitelyPresented.comap_of_finiteFree {d : ℕ}
    (e : (Mod.comap φ).obj (regular S) ≅ finiteFree R d) {N : Mod C S}
    (h : IsFinitelyPresented S N) : IsFinitelyPresented R ((Mod.comap φ).obj N) := by
  obtain ⟨n, m, f, ⟨e'⟩⟩ := h
  exact ⟨n * d, m * d,
    (comapFiniteFreeIso φ e m).inv ≫ (Mod.comap φ).map f ≫ (comapFiniteFreeIso φ e n).hom,
    ⟨(Mod.comap φ).mapIso e' ≪≫ PreservesCokernel.iso _ f ≪≫
      cokernel.mapIso _ _ (comapFiniteFreeIso φ e m) (comapFiniteFreeIso φ e n) (by simp)⟩⟩

end CategoryTheory.Mod
